# mathdoc_agent

`mathdoc_agent` decomposes mathematical documents into structured JSON using
Python-owned orchestration. The tree state, node IDs, statuses, validation, and
replacement logic live in Python; agents only perform bounded local refinement
tasks.

The package is separate from `json_agent`.

## Output Shape

The public JSON export is intended to be close to `resources/PaperStructure.json`.
It uses `type` discriminators such as:

- `document`
- `theorem`
- `structure-definition`
- `instance-definition`
- `inductive-type-definition`
- `proof_details`
- `induction_proof`
- `multi-condition_cases_proof`
- `assert_statement`

Internal Python models still use `kind` for handler dispatch, but
`mathdoc_agent.export.json.to_json` removes internal `kind` fields from exported
JSON.

`paragraph` is reserved for genuinely non-mathematical prose: motivation,
history, transitions, or commentary that makes no mathematical assertion and
introduces no mathematical object. Mathematical content should be represented as
definitions, theorem-like statements, structure/instance/inductive definitions,
proofs, calculations, examples, remarks, local claims, or `unknown` when the
parser cannot classify it safely.

For `inductive-type-definition`, constructor `arguments` are structured objects:

```json
{
  "name": "step_even",
  "arguments": [
    { "name": "n", "type": "Nat", "binder": "default" },
    { "name": "h", "type": "Even n", "binder": "default" }
  ],
  "index_args": ["n + 2"]
}
```

The optional `index_args` field gives the index values of the inductive family
for that constructor. Constructor argument `binder` is optional and may be
`default`, `implicit`, or `typeclass`; omitted means `default`.

## Command Line: Fake-Agent Examples

Run commands from the repository root.

For the induction plus cases example:

```bash
PYTHONPYCACHEPREFIX=/private/tmp/leanaide_pycache \
./venv/bin/python -m mathdoc_agent.examples.even_induction_cases
```

This writes:

```text
mathdoc_agent/examples/even_induction_cases.json
```

Generate Lean code from the JSON:

```bash
lake exe codegen mathdoc_agent/examples/even_induction_cases.json
```

This writes:

```text
CodeGen/even_induction_cases.lean
```

For a small corpus covering several proof types:

```bash
PYTHONPYCACHEPREFIX=/private/tmp/leanaide_pycache \
./venv/bin/python -m mathdoc_agent.examples.proof_type_examples
```

This writes `.md` and `.json` files to:

```text
mathdoc_agent/examples/proof_type_examples/
```

These examples use fake agents, so they do not require network access or API
keys.

## Command Line: Source Pipeline

Generate JSON from a source Markdown/text file:

```bash
PYTHONPYCACHEPREFIX=/private/tmp/leanaide_pycache \
./venv/bin/python -m mathdoc_agent.pipeline path/to/source.md \
  -o path/to/output.json
```

To also generate Lean code from the saved JSON, add `--lean`:

```bash
PYTHONPYCACHEPREFIX=/private/tmp/leanaide_pycache \
./venv/bin/python -m mathdoc_agent.pipeline path/to/source.md \
  -o path/to/output.json \
  --lean
```

The `--lean` option runs:

```bash
lake exe codegen path/to/output.json
```

It requires `-o/--output`; when JSON is written to stdout there is no JSON file
for Lean codegen to consume.

## Python: Fake Agents

Use fake agents when you want deterministic tests or fixtures.

```python
import asyncio

from mathdoc_agent.examples.even_induction_cases import (
    SOURCE_TEXT,
    build_registries,
)
from mathdoc_agent.export.json import to_json
from mathdoc_agent.orchestration.document_orchestrator import (
    document_from_text,
    refine_math_document,
)


async def main():
    document_registry, proof_registry = build_registries()
    document = document_from_text(
        SOURCE_TEXT,
        id="example",
        title="Example",
    )
    refined = await refine_math_document(
        document,
        document_registry,
        proof_registry,
    )
    print(to_json(refined))


asyncio.run(main())
```

## Python: Live API-Backed Agents

The default registries use the agents defined in `mathdoc_agent.mathagents.definitions`.
Those definitions use the OpenAI Agents SDK if it is installed. Set the model with
`MATHDOC_AGENT_MODEL`; otherwise the package default is used.

```bash
export OPENAI_API_KEY="..."
export MATHDOC_AGENT_MODEL="gpt-5.5"
```

Then:

```python
import asyncio

from mathdoc_agent.pipeline import generate_math_document_json


source_text = """
Theorem. For every natural number n, either n is even or n+1 is even.

Proof. We prove this by induction on n. For n=0, n is even. For the induction
step, assume either n is even or n+1 is even. Split into cases. If n is even,
then n+2 is even. If n+1 is even, the desired disjunction is immediate.
"""


async def main():
    json_text = await generate_math_document_json(
        source_text,
        id="live_example",
        title="Live Example",
    )
    print(json_text)


asyncio.run(main())
```

For synchronous scripts:

```python
from mathdoc_agent.pipeline import generate_math_document_json_sync

json_text = generate_math_document_json_sync(
    "Theorem. ...\n\nProof. ...",
    id="live_example",
    title="Live Example",
)
print(json_text)
```

## Command Line: Source Files

To generate JSON from a source text or Markdown file with the default live
API-backed agents. The command includes a final LLM-backed claim audit so every
exported `claim` field is shaped as a mathematical proposition for the Lean
`CodegenCore`/`PaperCodes` handlers; pass `--skip-claim-audit` only for
debugging that final pass.

```bash
export OPENAI_API_KEY="..."
export MATHDOC_AGENT_MODEL="gpt-5.5"

PYTHONPYCACHEPREFIX=/private/tmp/leanaide_pycache \
./venv/bin/python -m mathdoc_agent.pipeline \
  path/to/source.md \
  --title "Source Title" \
  --id source_id \
  -o path/to/source.json
```

If `-o/--output` is omitted, the JSON is printed to stdout:

```bash
PYTHONPYCACHEPREFIX=/private/tmp/leanaide_pycache \
./venv/bin/python -m mathdoc_agent.pipeline path/to/source.md
```

## Tests

Run:

```bash
PYTHONPYCACHEPREFIX=/private/tmp/leanaide_pycache \
./venv/bin/python -m unittest discover mathdoc_agent/tests
```

Compile check:

```bash
PYTHONPYCACHEPREFIX=/private/tmp/leanaide_pycache \
./venv/bin/python -m compileall mathdoc_agent
```

`PYTHONPYCACHEPREFIX` keeps Python bytecode caches inside a writable location on
this macOS sandbox.

## Main Modules

- `mathdoc_agent.pipeline`: public programmatic entry points.
- `mathdoc_agent.models`: Pydantic models for document/proof trees.
- `mathdoc_agent.handlers`: refinement handlers.
- `mathdoc_agent.plugins`: default registry factories.
- `mathdoc_agent.orchestration`: worklist and refinement loops.
- `mathdoc_agent.export.json`: PaperStructure-style JSON export.
- `mathdoc_agent.examples`: deterministic example generators.
