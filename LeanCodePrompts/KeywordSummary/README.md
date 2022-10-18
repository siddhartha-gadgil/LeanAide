# Keyword-based prompting

Keyword-based prompting is meant to extract the keywords from a given sentence and fetch similar definitions and theorem statements from `mathlib`. Keyword-based prompting complements sentence-similarity search.

The keyword extraction and search tool has multiple components.

## A database of mathematical keywords

Extracting mathematical keywords from a given sentence can be done by matching against a database of known mathematical keywords. This has the advantage of being fast (when suitable optimisations are made), extensible and specific to the domain of mathematics, and can be done entirely within `Lean4` without the need of external tools.

Good sources of mathematical keywords include `Wiktionary`, `Wikipedia` and `arXiv`.

## Organising the database for search

A [Trie](https://en.wikipedia.org/wiki/Trie) is a good data-structure to organise the database into for efficient search. This is reasonably straightforward to implement in `Lean4`. 

## Extracting keywords from a sentence

With a database of mathematical keywords available, keyword extraction can be done by either exact or approximate string matching. This step depends heavily on the quality of the keyword database. More sophisticated techniques may be needed to account for synonyms and close variations of the same word (like `Isomorphism`, `isomorphism`, `isomorphisms` and `isomorphic`).

## Pre-processing and storing `mathlib` statements

The next step is to gather the data of all the `mathlib` statements that contain a given mathematical keyword. For this, it is sufficient to run the keyword extraction procedure once on all of the `mathlib` data and then bucket sentences by keyword (with each sentence being in possibly many buckets). A crude notion of _relevance_ of a keyword to a sentence can be the number of times a given keyword occurs in a sentence divided by the total number of keywords in that sentence. For convenience, the buckets of keywords can also be sorted by relevance. 

Further streamlining like discarding extremely common keywords, discarding keywords that do not occur in `mathlib`, and retaining only the top few sentences (ordered by relevance) for each keyword can be done.

## Generating a prompt

The final goal is to retrieve `mathlib` statements similar to a given one using keywords. The first step will be to extract the keywords from the given sentence. Next, using a `HashMap`, one can fetch `mathlib` statements containing these keywords - using heuristics based on keyword relevance to decide which and how many of each to fetch.

---