import tempfile, shutil, os
from threading import Lock
from urlparse import urlparse

try:
    from cStringIO import StringIO
except ImportError:
    from StringIO import StringIO


class Serializer(object):

    def __init__(self, store):
        self.encoding = "UTF-8"
        self.base = None
        self.store = store

    def relativize(self, uri):
        base = self.base
        if base is not None and uri.startswith(base):
            uri = URIRef(uri.replace(base, "", 1))
        return uri

    def serialize(self, destination=None, format="xml", base=None, encoding=None, **args):
        if destination is None:
            stream = StringIO()
            self.store.serialize(stream, base=base, encoding=encoding)
            return stream.getvalue()
        if hasattr(destination, "write"):
            stream = destination
            self.store.serialize(stream, base=base, encoding=encoding)
        else:
            location = destination
            try:
                self.__save_lock.acquire()
                scheme, netloc, path, params, query, fragment = urlparse(location)
                if netloc!="":
                    print "WARNING: not saving as location is not a local file reference"
                    return
                name = tempfile.mktemp()
                stream = open(name, 'wb')
                self.store.serialize(stream, base=base, encoding=encoding, **args)
                stream.close()
                if hasattr(shutil,"move"):
                    shutil.move(name, path)
                else:
                    shutil.copy(name, path)
                    os.remove(name)
            finally:
                self.__save_lock.release()
