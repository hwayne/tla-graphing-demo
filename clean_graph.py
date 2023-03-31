from pathlib import Path
from argparse import ArgumentParser
import re 


def next_id_str(i):
    # convert number to string, 1 = a, 2 = b, 26 = z, 27 = aa, 28 = ab, etc.
    result = ""
    while i > 0:
        i = i - 1
        result = chr(ord('a') + int((i % 26))) + result
        i = i // 26
    return result

def main(file):
    i = 0
    mapping = {}
    graph = Path(file).read_text()

    regex = re.compile(r"-?[0-9]{10,}")

    for match in regex.finditer(graph):
        node = match.group()
        if not node in mapping.keys():
            i = i + 1
            mapping[node] = next_id_str(i)
            graph = graph.replace(match.group(), mapping[node])
    print(graph)

def parse_args():
    parser = ArgumentParser()
    parser.add_argument("file", help="graph file to process. Should be a graphviz dotfile")
    return parser.parse_args()

if __name__ == "__main__":
    args = parse_args()
    main(args.file)
    
