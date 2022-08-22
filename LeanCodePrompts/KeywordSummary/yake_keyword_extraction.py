import yake

def tuplelist2str(tl) -> str:
    return '\n\n'.join(map(lambda pr: pr[0] + ', ' + str(pr[1]), tl))

def yake_extract(s:str):
    keywords = yake.KeywordExtractor().extract_keywords(s)
    # further refinements will come here
    return keywords

def frequency_summary(cutoff = 0.3):
    # Read the file and extract keywords from each line
    f = open("../../data/clean_prompt_statements.txt", "r")
    docstrs = f.readlines()
    # Count the frequency of each keyword
    keyword_frequencies = {}
    for docstr in docstrs:
        for (kw, score) in yake_extract(docstr):
            if score < cutoff:
                if kw in keyword_frequencies:
                    keyword_frequencies[kw] += 1
                else:
                    keyword_frequencies[kw] = 1
    # Sort the keyword_frequencies dictionary in place by frequency
    sorted_keyword_frequencies = sorted(keyword_frequencies.items(), key=lambda kv: kv[1], reverse=True)
    # Write the keywords with frequency greater than the cutoff to a file `frequency_summary.txt`
    with open("frequency_summary.txt", "w") as out:
        for (kw, freq) in sorted_keyword_frequencies:
            if freq > 1:
                out.write(kw + ", " + str(freq) + "\n")
            
def frequency_summary_mathlib_json():
    import json
    f = open("../../data/clean_prompt_statements.txt", "r")
    docstrs = f.readlines()
    # Create a `keyword_statement_summary` dictionary
    keyword_statement_summary = [{"docstring": docstr, "keywords" : dict(yake_extract(docstr))} 
        for docstr in docstrs]
    # Output to a JSON file
    with open("mathlib_keyword_summary.json", "w") as out:
        json.dump(keyword_statement_summary, out)
        
def main():
    with open("yake_keyword_extraction_results.md", "w+") as out:
        out.write("# Yake keyword extaction experiment")
        with open("docstrings.txt", "r") as f:
            docstrs = f.readlines()
            for i, docstr in enumerate(docstrs):
                out.write("\n\n## Example " + str(i) + '\n')
                print(docstr)
                out.write("\n### Statement" + '\n' + docstr + '\n')
                yake_outputs = tuplelist2str(yake_extract(docstr))
                out.write("### Keywords" + '\n' + yake_outputs + '\n')         

frequency_summary_mathlib_json()