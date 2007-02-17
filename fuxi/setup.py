from distutils.core import setup
setup(name="FuXi",
      version="0.8b",
      description="A N3-based forward-chaining, DL reasoner for RDFLib",
      author="Chime Ogbuji",
      author_email="chimezie@ogbuji.net",
      package_dir = {
        'FuXi': 'lib',
      },
      packages=[
        "FuXi",
        "FuXi.Rete"
      ]
)