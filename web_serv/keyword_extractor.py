import yake

def extract_keywords(stmt : str, n:int = 10) -> [str] :
    kw_extractor = yake.KeywordExtractor(n=n)
    return kw_extractor.extract_keywords(stmt)