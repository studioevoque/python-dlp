#download ez_setup.py from http://peak.telecommunity.com/dist/ez_setup.py
#import ez_setup
#ez_setup.use_setuptools()
from setuptools  import setup
setup(name="Triclops",
      version="0.99a",
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
        '4Suite-XML>=1.0.2',
        'Paste>=1.1.1',
        'PasteScript',        
        'Beaker',
        'wsgiutils',
        'Amara'
      ],
      license = "CC",
      keywords = "python rdf sparql query",
      url = "http://code.google.com/p/python-dlp/wiki/Triclops",
      entry_points = """
      [paste.app_factory]
      entailmentManager = Triclops.wsgiapp:make_entailment_manager
      main   = Triclops.wsgiapp:make_app
      usher  = Triclops.wsgiapp:make_usher
      about  = Triclops.wsgiapp:make_about
      owlBrowser  = Triclops.wsgiapp:make_owlBrowser
      browse = Triclops.wsgiapp:make_browser
      queryMgr = Triclops.wsgiapp:make_query_manager
      ticketManager = Triclops.wsgiapp:make_ticket_manager
      form = Triclops.wsgiapp:make_form_manager
      """,
      zip_safe=False
)