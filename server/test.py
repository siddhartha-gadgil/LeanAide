from __future__ import annotations
import streamlit as st
import os
from pydantic import BaseModel, Field, ConfigDict
from openai import OpenAI
from dotenv import load_dotenv
import json
load_dotenv()

from datetime import date
from enum import Enum
from typing import List, Optional, Union
from pydantic import RootModel

OPENAI_API_KEY = os.getenv("OPENAI_API_KEY")
client = OpenAI(
    api_key=OPENAI_API_KEY
)

class Title(BaseModel):
    model_config = ConfigDict(extra='forbid')

    type: str = Field(
        default='Title', frozen=True, description='The type of this document element.'
    )
    title: str = Field(..., description='The title text.')


class Abstract(BaseModel):
    model_config = ConfigDict(extra='forbid')

    type: str = Field(
        default='Abstract', frozen=True, description='The type of this document element.'
    )
    abstract: str = Field(..., description='The abstract text.')


class Header(Enum):
    Theorem = 'Theorem'
    Lemma = 'Lemma'
    Proposition = 'Proposition'
    Corollary = 'Corollary'
    Claim = 'Claim'


class Header1(Enum):
    Definition = 'Definition'
    Notation = 'Notation'
    Terminology = 'Terminology'
    Convention = 'Convention'


class Header2(Enum):
    Remark = 'Remark'
    Example = 'Example'
    Note = 'Note'
    Observation = 'Observation'
    Warning = 'Warning'


class LetStatement(BaseModel):
    model_config = ConfigDict(extra='forbid')

    type: str = Field(
        default='let_statement', frozen=True, description='The type of this logical step.'
    )
    variable_name: str = Field(
        ...,
        description='The variable being defined (use `<anonymous>` if there is no name such as in `We have a group structure on S`)',
    )
    value: Optional[str] = Field(
        None, description='(OPTIONAL) The value of the variable being defined'
    )
    variable_type: Optional[str] = Field(
        None,
        description='(OPTIONAL) The type of the variable, such as `real number`, `function from S to T`, `element of G` etc.',
    )
    properties: Optional[str] = Field(
        None,
        description='(OPTIONAL) Specific properties of the variable beyond the type',
    )


class SomeStatement(BaseModel):
    model_config = ConfigDict(extra='forbid')

    type: str = Field(
        default='some_statement', frozen=True, description='The type of this logical step.'
    )
    variable_name: str = Field(
        ...,
        description='The variable being defined (use `<anonymous>` if there is no name such as in `We have a group structure on S`)',
    )
    variable_kind: Optional[str] = Field(
        None,
        description='(OPTIONAL) The type of the variable, such as `real number`, `function from S to T`, `element of G` etc.',
    )
    properties: Optional[str] = Field(
        None,
        description='(OPTIONAL) Specific properties of the variable beyond the type',
    )


class ResultsUsedItem(BaseModel):
    model_config = ConfigDict(extra='forbid')

    statement: str = Field(..., description='The statement of the result used.')
    target_identifier: Optional[str] = Field(
        None,
        description="(OPTIONAL) The unique 'label' of the document element being referenced (e.g., 'sec:intro', 'thm:main', 'fig:diagram').",
    )


class CalculationStep(RootModel):
    root: str = Field(
        ...,
        description='A step, typically an equality or inequality, in a calculation or computation.',
    )


class ConcludeStatement(BaseModel):
    model_config = ConfigDict(extra='forbid')

    type: str = Field(
        default='conclude_statement', frozen=True, description='The type of this logical step.'
    )
    claim: str = Field(..., description='The conclusion of the proof.')


class Author(BaseModel):
    model_config = ConfigDict(extra='forbid')

    name: str = Field(..., description='Full name of the author.')
    affiliation: Optional[str] = Field(
        None, description="(OPTIONAL) Author's affiliation."
    )


class Figure(BaseModel):
    model_config = ConfigDict(extra='forbid')

    type: str = Field(
        default='Figure', frozen=True, description='The type of this document element.'
    )
    label: str = Field(
        ...,
        description="Unique identifier/label for referencing (e.g., 'fig:flowchart').",
    )
    source: str = Field(..., description='URL or path to the image file.')
    caption: Optional[str] = Field(
        None, description='(OPTIONAL) Caption describing the figure.'
    )
    alt_text: Optional[str] = Field(
        None, description='(OPTIONAL) Alternative text for accessibility.'
    )


class Table(BaseModel):
    model_config = ConfigDict(extra='forbid')

    type: str = Field(
        default='Table', frozen=True, description='The type of this document element.'
    )
    label: str = Field(
        ...,
        description="Unique identifier/label for referencing (e.g., 'tab:results').",
    )
    caption: Optional[str] = Field(
        None, description='(OPTIONAL) Caption describing the table.'
    )
    content: List[List[str]] = Field(
        ...,
        description='Table data, represented as an array of rows, where each row is an array of cell strings.',
    )
    header_row: Optional[bool] = Field(
        False,
        description="(OPTIONAL) Indicates if the first row in 'content' is a header row. Default: false",
    )


class BibliographyEntry(BaseModel):
    model_config = ConfigDict(extra='forbid')

    key: str = Field(
        ..., description="Unique key used for citations (e.g., 'Knuth1974', '[1]')."
    )
    formatted_entry: str = Field(
        ...,
        description='The full bibliographic reference, formatted as text (e.g., APA, BibTeX style).',
    )


class Citation(BaseModel):
    model_config = ConfigDict(extra='forbid')

    cite_keys: List[str] = Field(
        ..., description='An array of bibliography keys being cited.', min_length=1
    )


class InternalReference(BaseModel):
    model_config = ConfigDict(extra='forbid')

    target_identifier: str = Field(
        ...,
        description="The unique 'label' of the document element being referenced (e.g., 'sec:intro', 'thm:main', 'fig:diagram').",
    )


class Definition(BaseModel):
    model_config = ConfigDict(extra='forbid')

    type: str = Field(
        default='Definition', frozen=True, description='The type of this document element.'
    )
    definition: str = Field(..., description='Definition content.')
    label: str = Field(..., description='Definition identifier.')
    header: Header1 = Field(..., description='The definition type.')
    citations: Optional[List[Citation]] = Field(
        None,
        description='(OPTIONAL) Explicit list of citations relevant to this theorem statement.',
    )
    internal_references: Optional[List[InternalReference]] = Field(
        None,
        description='(OPTIONAL) Explicit list of internal references mentioned in the theorem statement.',
    )


class Remark(BaseModel):
    model_config = ConfigDict(extra='forbid')

    type: str = Field(
        default='Remark', frozen=True, description='The type of this document element.'
    )
    remark: str = Field(..., description='Remark content.')
    label: str = Field(..., description='Remark identifier.')
    header: Header2 = Field(..., description='Remark type.')
    citations: Optional[List[Citation]] = Field(
        None,
        description='(OPTIONAL) Explicit list of citations relevant to this statement.',
    )
    internal_references: Optional[List[InternalReference]] = Field(
        None,
        description='(OPTIONAL) Explicit list of internal references mentioned in the statement.',
    )


class AssumeStatement(BaseModel):
    model_config = ConfigDict(extra='forbid')

    type: str = Field(
        default='assume_statement', frozen=True, description='The type of this logical step.'
    )
    assumption: str = Field(..., description='The assumption text.')
    label: Optional[str] = Field(
        None, description='(OPTIONAL) The label of the assumption, if any.'
    )
    citations: Optional[List[Citation]] = Field(
        None,
        description='(OPTIONAL) Citations supporting or related to the assumption.',
    )
    internal_references: Optional[List[InternalReference]] = Field(
        None, description='(OPTIONAL) Internal references related to the assumption.'
    )


class Calculation(BaseModel):
    inline_calculation: Optional[str] = Field(
        None,
        description='A simple calculation or computation written as a single line.',
    )
    calculation_sequence: Optional[List[CalculationStep]] = Field(
        None, description='A list of elements of type `calculation_step`.'
    )


class Metadata(BaseModel):
    model_config = ConfigDict(extra='forbid')

    type: str = Field(
        default='Metadata', frozen=True, description='The type of this document element.'
    )
    authors: List[Author] = Field(..., description='List of authors.')
    keywords: Optional[List[str]] = Field(
        None, description='List of keywords describing the document.'
    )
    msc_codes: Optional[List[str]] = Field(
        None, description='Mathematics Subject Classification codes.'
    )
    publication_date: Optional[date] = Field(
        None,
        description='Date of publication or creation (ISO 8601 format recommended).',
    )
    source: Optional[str] = Field(
        None,
        description='Publication source, e.g., Journal label, volume, pages, conference proceedings.',
    )


class Paragraph(BaseModel):
    model_config = ConfigDict(extra='forbid')

    type: str = Field(
        default='Paragraph', frozen=True, description='The type of this document element.'
    )
    text: str = Field(
        ...,
        description="The main text content of the paragraph. Inline citations (e.g., [1], [Knuth74]) and internal references (e.g., see Section 2, Theorem 3) might be embedded within this string or explicitly listed in 'citations'/'internal_references'.",
    )
    citations: Optional[List[Citation]] = Field(
        None,
        description='(OPTIONAL) Explicit list of citations mentioned in this paragraph.',
    )
    internal_references: Optional[List[InternalReference]] = Field(
        None,
        description='(OPTIONAL) Explicit list of internal references mentioned in this paragraph.',
    )


class Bibliography(BaseModel):
    model_config = ConfigDict(extra='forbid')

    type: str = Field(
        default='Bibliography', frozen=True, description='The type of this document element.'
    )
    header: str = Field(
        ..., description="The section header (e.g., 'References', 'Bibliography')."
    )
    entries: List[BibliographyEntry] = Field(
        ..., description='List of bibliography entries.'
    )


class AssertStatement(BaseModel):
    model_config = ConfigDict(extra='forbid')

    type: str = Field(
        default='assert_statement', frozen=True, description='The type of this logical step.'
    )
    claim: str = Field(
        ...,
        description='The mathematical claim being asserted, NOT INCLUDING proofs, justifications or results used. The claim should be purely a logical statement which is the *consequence* obtained.',
    )
    proof_method: Optional[str] = Field(
        None,
        description='(OPTIONAL) The method used to prove the claim. This could be a direct proof, proof by contradiction, proof by induction, etc. this should be a single phrase or a fairly simple sentence; if a longer justification is needed break the step into smaller steps. If the method is deduction from a result, use `citations`or `internal_references`.',
    )
    label: Optional[str] = Field(
        None,
        description='The label of the statement, if any. If this statement is used in a proof or as justification for an assertion, it should be labeled so that it can be referenced later.',
    )
    citations: Optional[List[Citation]] = Field(
        None,
        description='(OPTIONAL) Explicit list of citations relevant to this theorem statement.',
    )
    results_used: Optional[List[ResultsUsedItem]] = Field(
        None,
        description='(OPTIONAL) Explicit list of results used in the proof, for example where the assertion says "using ...". Include both standard results and results from the document itself, with references where available.',
    )
    internal_references: Optional[List[InternalReference]] = Field(
        None,
        description='(OPTIONAL) Explicit list of internal references mentioned in the theorem statement.',
    )
    calculation: Optional[Calculation] = Field(
        None, description='(OPTIONAL) An equation, inequality, short calculation etc.'
    )


class Section(BaseModel):
    model_config = ConfigDict(extra='forbid')

    type: str = Field(
        default='Section', frozen=True, description='The type of this document element.'
    )
    content: List[
        Union[
            'Section',
            'Theorem',
            'Definition',
            'Remark',
            'LogicalStepSequence',
            'Paragraph',
            'Proof',
            'Figure',
            'Table',
        ]
    ] = Field(..., description='The content of the section.')
    label: str = Field(..., description='Section identifier.')
    level: Optional[int] = Field(
        None,
        description='The section level such as `1` for a section, `2` for a subsection.',
    )
    header: str = Field(..., description='The section header.')


class Theorem(BaseModel):
    model_config = ConfigDict(extra='forbid')

    type: str = Field(
        default='Theorem', frozen=True, description='The type of this document element.'
    )
    hypothesis: Optional[List[Union[LetStatement, AssumeStatement, SomeStatement]]] = (
        Field(
            None,
            description="(OPTIONAL) The hypothesis or assumptions of the theorem, consisting of statements like 'let', 'assume', etc.",
        )
    )
    claim: str = Field(..., description='The statement.')
    label: str = Field(
        ...,
        description="Unique identifier/label for referencing (e.g., 'thm:main', 'lem:pumping').",
    )
    proof: Optional['Proof'] = Field(
        None,
        description='Proof of the theorems, if it is present soon after the statement.',
    )
    header: Header = Field(
        ...,
        description='The type of theorem-like environment. Must be one of the predefined values.',
    )
    citations: Optional[List[Citation]] = Field(
        None,
        description='(OPTIONAL) Explicit list of citations relevant to this statement.',
    )
    internal_references: Optional[List[InternalReference]] = Field(
        None,
        description='(OPTIONAL) Explicit list of internal references mentioned in the statement.',
    )


class LogicalStepSequence(RootModel):
    root: List[
        Union[
            LetStatement,
            AssertStatement,
            AssumeStatement,
            SomeStatement,
            'PatternCasesStatement',
            'BiImplicationCasesStatement',
            'ConditionCasesStatement',
            'MultiConditionCasesStatement',
            'InductionStatement',
            Calculation,
            'ContradictionStatement',
            ConcludeStatement,
        ]
    ] = Field(
        ...,
        description="A sequence of structured logical steps, typically used within a proof or derivation, consisting of statements like 'let', 'assert', 'assume', etc.",
    )


class Proof(BaseModel):
    model_config = ConfigDict(extra='forbid')

    type: str = Field(
        default='Proof', frozen=True, description='The type of this document element.'
    )
    claim_label: str = Field(..., description='Theorem label being proved.')
    proof_steps: List[Union[Remark, LogicalStepSequence, Paragraph, Figure, Table]] = (
        Field(..., description='Steps in the proof.')
    )


class PatternCasesStatement(BaseModel):
    model_config = ConfigDict(extra='forbid')

    type: str = Field(
        default='pattern_cases_statement',
        frozen=True,
        description='The type of this logical step.',
    )
    on: str = Field(
        ...,
        description='The variable or expression which is being matched against patterns.',
    )
    proof_cases: List['PatternCase'] = Field(
        ..., description='A list of elements of type `case`.'
    )


class BiImplicationCasesStatement(BaseModel):
    model_config = ConfigDict(extra='forbid')

    type: str = Field(
        default='bi-implication_cases_statement',
        frozen=True,
        description='The type of this logical step.',
    )
    if_proof: 'Proof' = Field(..., description='Proof that `P` implies `Q`.')
    only_if_proof: 'Proof' = Field(..., description='Proof that `Q` implies `P`.')


class ConditionCasesStatement(BaseModel):
    model_config = ConfigDict(extra='forbid')

    type: str = Field(
        default='condition_cases_statement',
        frozen=True,
        description='The type of this logical step.',
    )
    condition: str = Field(
        ..., description='The condition based on which the proof is split.'
    )
    true_case_proof: 'Proof' = Field(
        ..., description='Proof of the case where the condition is true.'
    )
    false_case_proof: 'Proof' = Field(
        ..., description='Proof of the case where the condition is false.'
    )


class MultiConditionCasesStatement(BaseModel):
    model_config = ConfigDict(extra='forbid')

    type: str = Field(
        default='multi-condtion_cases_statement',
        frozen=True,
        description='The type of this logical step.',
    )
    proof_cases: List['ConditionCase'] = Field(
        ..., description='The conditions and proofs in the different cases.'
    )
    exhaustiveness: Optional['Proof'] = Field(
        None, description='(OPTIONAL) Proof that the cases are exhaustive.'
    )


class PatternCase(BaseModel):
    model_config = ConfigDict(extra='forbid')

    type: str = Field(
        default='pattern_case', frozen=True, description='The type of this logical step.'
    )
    pattern: str = Field(..., description='The pattern determining this case.')
    proof: 'Proof' = Field(..., description='Proof of this case.')


class ConditionCase(BaseModel):
    model_config = ConfigDict(extra='forbid')

    type: str = Field(
        default='condition_case', frozen=True, description='The type of this logical step.'
    )
    condition: str = Field(..., description='The condition determining this case.')
    proof: 'Proof' = Field(..., description='Proof for this case.')


class Case(BaseModel):
    model_config = ConfigDict(extra='forbid')

    type: str = Field(default='case', frozen=True, description='The type of this logical step.')
    condition: str = Field(
        ...,
        description="The case condition or pattern; for induction one of 'base' or 'induction-step'; for a side of an 'iff' statement write the claim being proved (i.e., the statement `P => Q` or `Q => P`).",
    )
    proof: 'Proof' = Field(..., description='Proof of this case.')


class InductionStatement(BaseModel):
    model_config = ConfigDict(extra='forbid')

    type: str = Field(
        default='induction_statement', frozen=True, description='The type of this logical step.'
    )
    on: str = Field(
        ..., description='The variable or expression on which induction is being done.'
    )
    base_case_proof: 'Proof' = Field(..., description='Proof of the base case.')
    induction_step_proof: 'Proof' = Field(
        ...,
        description='Proof of the induction step, which typically shows that if the statement holds for `n`, it holds for `n+1`.',
    )


class ContradictionStatement(BaseModel):
    model_config = ConfigDict(extra='forbid')

    type: str = Field(
        default='contradiction_statement',
        frozen=True,
        description='The type of this logical step.',
    )
    assumption: str = Field(
        ..., description='The assumption being made to be contradicted.'
    )
    proof: 'Proof' = Field(
        ..., description='The proof of the contradiction given the assumption.'
    )

class MathematicalDocumentWrapper(BaseModel):
    model_config = ConfigDict(extra='forbid')

    document: List[
        Union[
            Title,
            Abstract,
            Metadata,
            Section,
            Theorem,
            Definition,
            Remark,
            LogicalStepSequence,
            Paragraph,
            Proof,
            Figure,
            Table,
            Bibliography,
        ]
    ] = Field(
        ...,
        description='The root of the mathematical document, containing a sequence of environments.',
    )

# Update forward references
MathematicalDocumentWrapper.model_rebuild()
Section.model_rebuild()
Theorem.model_rebuild()
LogicalStepSequence.model_rebuild()
PatternCasesStatement.model_rebuild()
MultiConditionCasesStatement.model_rebuild()


file = client.files.create(
    file=open("blms.70015.pdf", "rb"),
    purpose="user_data"
)


print("hi")
completion = client.chat.completions.create(
    model="o4-mini",  # or "gpt-5.1" when available
    messages=[
        {
            "role": "system",
            "content": "You are a helpful assistant that parses mathematical documents and gives structured json output in the given format. You have to strictly follow the format and make the output as deep and complex as possible."
        },
        {
            "role": "user",
            "content": [
                {
                    "type": "text",
                    "text": "Please parse this mathematical document and return structured output in the specified format."
                },
                {
                    "type": "file",
                    "file": {
                        "file_id": file.id,
                    }
                }
            ]
        }
    ],
    response_format={"type": "json_object"}
)

print(completion)

try:
    # Parse the JSON content from the response
    response_content = completion.choices[0].message.content
    parsed = json.loads(response_content)
    print(parsed)
    st.json(parsed)
    from st_copy import copy_button
    copy_button(parsed)
except Exception as e:
    print(f"Error parsing response: {e}")