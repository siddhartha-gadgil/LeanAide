"""Audit parsed document structure against the original source text."""

from __future__ import annotations

import os
import re
from collections import Counter
from typing import Any, Iterable

from mathdoc_agent.handlers.document_handlers import document_node_from_child_spec
from mathdoc_agent.mathagents.runner import run_agent_typed
from mathdoc_agent.models.base import DocumentKind
from mathdoc_agent.models.document import DocumentNode, MathDocument
from mathdoc_agent.models.refinement_specs import SourceCoverageAuditSpec
from mathdoc_agent.orchestration.document_orchestrator import recompute_document_statuses
from mathdoc_agent.orchestration.worklist import kind_key


DEFAULT_COVERAGE_THRESHOLD = 0.72
DEFAULT_MAX_SUSPECT_BLOCKS = 40

PROSE_NODE_KINDS = {
    DocumentKind.paragraph.value,
    DocumentKind.example.value,
    DocumentKind.remark.value,
    DocumentKind.proof.value,
    DocumentKind.opaque.value,
    DocumentKind.unknown.value,
}


def _coverage_threshold() -> float:
    raw = os.environ.get("MATHDOC_AGENT_SOURCE_COVERAGE_THRESHOLD")
    if raw is None:
        return DEFAULT_COVERAGE_THRESHOLD
    try:
        value = float(raw)
    except ValueError:
        return DEFAULT_COVERAGE_THRESHOLD
    return min(1.0, max(0.0, value))


def _max_suspect_blocks() -> int:
    raw = os.environ.get("MATHDOC_AGENT_SOURCE_COVERAGE_MAX_BLOCKS")
    if raw is None:
        return DEFAULT_MAX_SUSPECT_BLOCKS
    try:
        value = int(raw)
    except ValueError:
        return DEFAULT_MAX_SUSPECT_BLOCKS
    return max(1, value)


def source_blocks(source_text: str) -> list[dict[str, str]]:
    """Split Markdown into stable nonempty blocks for coverage comparison."""
    blocks: list[str] = []
    pending: list[str] = []

    def flush() -> None:
        text = "\n".join(pending).strip()
        if text:
            blocks.append(text)
        pending.clear()

    for line in source_text.splitlines():
        stripped = line.strip()
        if not stripped:
            flush()
            continue
        if stripped.startswith("#"):
            flush()
            blocks.append(stripped)
            continue
        pending.append(line.rstrip())
    flush()
    return [
        {"id": f"source-block-{index + 1}", "text": text}
        for index, text in enumerate(blocks)
    ]


def _coverage_tokens(text: str) -> list[str]:
    replacements = {
        r"\mathbb{R}": " R ",
        r"\mathbb{Z}": " Z ",
        r"\mathbb{N}": " N ",
        r"\leq": " <= ",
        r"\geq": " >= ",
        r"\neq": " != ",
        r"\to": " -> ",
        r"\in": " in ",
        "≤": " <= ",
        "≥": " >= ",
        "≠": " != ",
        "→": " -> ",
        "⁻¹": " inverse ",
    }
    normalized = text
    for source, replacement in replacements.items():
        normalized = normalized.replace(source, replacement)
    normalized = re.sub(r"\\(?:operatorname|mathrm|text)\{([^{}]*)\}", r" \1 ", normalized)
    normalized = re.sub(r"\\[A-Za-z]+", " ", normalized)
    normalized = re.sub(r"[*_`#$\\{}()[\],.:;|]+", " ", normalized)
    return [token.casefold() for token in re.findall(r"[A-Za-z0-9]+|<=|>=|!=|->", normalized)]


def _token_recall(source: str, candidate: str) -> float:
    source_tokens = Counter(_coverage_tokens(source))
    if not source_tokens:
        return 1.0
    candidate_tokens = Counter(_coverage_tokens(candidate))
    overlap = sum(
        min(count, candidate_tokens[token])
        for token, count in source_tokens.items()
    )
    return overlap / sum(source_tokens.values())


def _strings(value: Any) -> Iterable[str]:
    if isinstance(value, str):
        yield value
    elif isinstance(value, dict):
        for item in value.values():
            yield from _strings(item)
    elif isinstance(value, list):
        for item in value:
            yield from _strings(item)


def _node_corpus(node: DocumentNode) -> str:
    node_kind = kind_key(node.kind)
    values: list[str] = [node.title or "", node.label or ""]
    # For prose nodes, the text is the generated representation. For definitions
    # and theorem statements, it is retained source evidence and must not conceal
    # lossy structured fields (the exact failure this pass is intended to catch).
    if node_kind in PROSE_NODE_KINDS:
        values.append(node.text)
    values.extend(_strings(node.data))
    if node.proof is not None:
        values.append(node.proof.root.text)
        values.extend(_strings(node.proof.root.data))
    return "\n".join(value for value in values if value)


def _child_summary(node: DocumentNode) -> dict[str, Any]:
    summary: dict[str, Any] = {
        "id": node.id,
        "kind": kind_key(node.kind),
        "label": node.label,
        "title": node.title,
        "text": node.text,
        "data": node.data,
        "has_proof": node.proof is not None,
    }
    if node.proof is not None:
        summary["proof_text"] = node.proof.root.text
    return summary


def source_coverage_entries(
    document: MathDocument,
    source_text: str,
) -> list[dict[str, Any]]:
    """Return source blocks whose token recall is below the configured threshold."""
    children = document.root.children
    corpora = [(node, _node_corpus(node)) for node in children]
    entries: list[dict[str, Any]] = []
    for block in source_blocks(source_text):
        tokens = _coverage_tokens(block["text"])
        if len(tokens) < 3:
            continue
        ranked = sorted(
            (
                (_token_recall(block["text"], corpus), node)
                for node, corpus in corpora
            ),
            key=lambda item: item[0],
            reverse=True,
        )
        best_score = ranked[0][0] if ranked else 0.0
        if best_score >= _coverage_threshold():
            continue
        entries.append(
            {
                **block,
                "coverage_score": round(best_score, 3),
                "nearest_children": [
                    _child_summary(node)
                    for _, node in ranked[:3]
                ],
            }
        )
    return entries[: _max_suspect_blocks()]


def apply_source_coverage_patches(
    document: MathDocument,
    spec: SourceCoverageAuditSpec,
) -> MathDocument:
    """Apply validated root-child insertions and replacements."""
    children = list(document.root.children)
    for patch in spec.patches:
        if patch.action == "replace_child":
            if not patch.target_id:
                continue
            index = next(
                (i for i, child in enumerate(children) if child.id == patch.target_id),
                None,
            )
            if index is None:
                continue
            children[index] = document_node_from_child_spec(
                document.root.id,
                patch.child,
                child_id=patch.target_id,
            )
            continue

        if patch.action != "insert_child":
            continue
        child = document_node_from_child_spec(document.root.id, patch.child)
        if any(existing.id == child.id for existing in children):
            continue
        if patch.after_id is None:
            children.append(child)
            continue
        index = next(
            (i for i, existing in enumerate(children) if existing.id == patch.after_id),
            None,
        )
        if index is not None:
            children.insert(index + 1, child)

    root = document.root.model_copy(
        update={
            "children": children,
            "notes": [*document.root.notes, *spec.notes],
        }
    )
    return document.model_copy(update={"root": recompute_document_statuses(root)})


async def audit_source_coverage(
    document: MathDocument,
    source_text: str,
    agent: Any | None,
) -> MathDocument:
    """Repair omitted or materially truncated source blocks before proof refinement."""
    entries = source_coverage_entries(document, source_text)
    if not entries or agent is None:
        return document
    spec = await run_agent_typed(
        agent,
        {
            "task": (
                "Audit source coverage after document parsing. Restore omitted source "
                "blocks and replace nodes whose mathematical content was materially "
                "truncated. Preserve exact formulas and attach proof text to theorem nodes."
            ),
            "source_blocks_needing_review": entries,
            "current_child_order": [child.id for child in document.root.children],
            "patch_rules": {
                "insert_child": (
                    "Insert a genuinely omitted source block after its preceding sibling."
                ),
                "replace_child": (
                    "Replace an existing child when its summary omitted hypotheses, fields, "
                    "equations, or other mathematical content. Return the complete child."
                ),
                "fidelity": (
                    "Use the source block verbatim or losslessly normalized; never replace "
                    "explicit formulas by a list of property names."
                ),
            },
        },
        SourceCoverageAuditSpec,
    )
    repaired = apply_source_coverage_patches(document, spec)
    remaining = source_coverage_entries(repaired, source_text)
    if remaining:
        root = repaired.root.model_copy(
            update={
                "notes": [
                    *repaired.root.notes,
                    "Source coverage still needs review for: "
                    + ", ".join(entry["id"] for entry in remaining),
                ]
            }
        )
        repaired = repaired.model_copy(update={"root": root})
    return repaired
