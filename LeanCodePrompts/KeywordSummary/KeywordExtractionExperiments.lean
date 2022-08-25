import LeanCodePrompts.KeywordSummary.KeywordExtraction

#eval fetchStatementsWithKeyword (·["statement"]!) "free group"

#eval keywordBasedPrompts docPair "The fundamental group of a circle is non-trivial." (kwds := true)

#eval keywordBasedPrompts docPair "Every subgroup of a free group is a free group." 0.1 (kwds := true)

#eval fetchStatementsWithKeyword (·["statement"]!) "non-trivial"


#eval fetchStatementsWithKeyword (·["statement"]!) "free"
