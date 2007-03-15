import ez_setup
ez_setup.use_setuptools()
from setuptools  import setup
setup(name="FuXi",
      version="0.85b",
      description="A N3-based forward-chaining, DL reasoner for RDFLib",
      author="Chime Ogbuji",
      author_email="chimezie@ogbuji.net",
      package_dir = {
        'FuXi': 'lib',
      },
      packages=[
        "FuXi",
        "FuXi.Rete"
      ],
      install_requires = ['rdflib>=2.3.3'],
      scripts = ['Fuxi.py'],
      license = "BSD",
      keywords = "python logic owl rdf dlp n3 rule reasoner",
      url = "http://code.google.com/p/python-dlp/wiki/FuXi",
      entry_points = {
       'console_scripts': [
           'Fuxi = FuXi.Rete.CommandLine:main',
        ],
      },
      zip_safe=False
)