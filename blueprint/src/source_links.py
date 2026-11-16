"""Resolve blueprint declarations to the checked integration-in-ACVF source revision."""
from pathlib import Path
SOURCE = "https://github.com/daviddhilbert/integration-in-ACVF/blob/862aa448b4314df673bccd928d1353af6650d7f1/"
def ProcessOptions(options, document):
    links = dict(line.split("\t") for line in Path(__file__).with_name("source-links.tsv").read_text(encoding="utf-8").splitlines())
    def set_source_links():
        for graph in document.userdata["dep_graph"]["graphs"].values():
            for node in graph.nodes:
                node.userdata["lean_urls"] = [(name, SOURCE + links[name]) for name in node.userdata.get("leandecls", [])]
    document.addPostParseCallbacks(160, set_source_links)

