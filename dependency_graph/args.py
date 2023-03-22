import argparse

def build_parser():
    parser = argparse.ArgumentParser( )

    parser.add_argument('--decl_name',type=str,required=True,help='declaration name')

    parser.add_argument('--output',type=str,required=True,help='output svg file name')

    return parser