import StatementAutoformalisation.SentenceSimilarityQuery

def CustomSentenceSimilarityParams : SentenceSimilarity.Params :=
{
  source := "data/safe-prompts.json",
  model := "all-mpnet-base-v2",
  kind := "theorem",
  field := "doc_string",
  nSim := 10
}