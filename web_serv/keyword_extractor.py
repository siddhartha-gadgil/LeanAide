import yake

def extract_keywords(stmt : str, n:int = 10):
    kw_extractor = yake.KeywordExtractor(n=n)
    keywords = kw_extractor.extract_keywords(stmt)
    return keywords