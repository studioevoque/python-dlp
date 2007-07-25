#download ez_setup.py from http://peak.telecommunity.com/dist/ez_setup.py
#import ez_setup
#ez_setup.use_setuptools()
from setuptools  import setup
setup(name="Triclops",
      version="0.4",
      description="A Paste-based SPARQL Server for RDFLib",
      author="Chime Ogbuji",
      author_email="chimezie@gmail.com",
      package_dir = {
        'Triclops': 'lib',
      },
      packages=[
        "Triclops",
      ],
      install_requires = [
        #'4Suite-XML>=1.0.2',
        'Paste>=1.1.1',
        'PasteScript',        
        #'rdflib>=2.3.3',
        'Beaker',
        #'wsgiutils',
      ],
      license = "CC",
      keywords = "python rdf sparql query",
      url = "http://code.google.com/p/python-dlp/wiki/Triclops",
      entry_points = """
      [paste.app_factory]
      main   = Triclops.wsgiapp:make_app
      usher  = Triclops.wsgiapp:make_usher
      about  = Triclops.wsgiapp:make_about
      browse = Triclops.wsgiapp:make_browser
      """,
      zip_safe=False
)