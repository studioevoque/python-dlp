"""
This module defines the WSGI entry point for this application.
"""
from Server import WsgiApplication, Usher, About, Browser
from paste.deploy.config import ConfigMiddleware
from paste import httpexceptions
from paste.urlparser import StaticURLParser, make_static
from paste.recursive import RecursiveMiddleware
from paste.urlmap import URLMap
from beaker.middleware import CacheMiddleware

def make_app(global_conf, **app_conf):
    # @@@ Core Application @@@
    app = WsgiApplication(global_conf)
    # @@@ Expose config variables to other plugins @@@
    app = ConfigMiddleware(app, {'app_conf':app_conf,
                                 'global_conf':global_conf})
    # @@@ Caching support from Beaker @@@
    app = CacheMiddleware(app, global_conf)
    # @@@ Change HTTPExceptions to HTTP responses @@@
    app = httpexceptions.make_middleware(app, global_conf)
    return app

def make_usher(global_conf, **app_conf):
    return Usher(global_conf)

def make_about(global_conf, **app_conf):
    return About(global_conf)

def make_browser(global_conf, **app_conf):
    return Browser(global_conf)