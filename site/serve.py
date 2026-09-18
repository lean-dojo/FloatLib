#!/usr/bin/env python3
"""Serve the built FloatLib site from local build storage.

A plain static server is almost enough, but the reader is a single-page app with hash routes,
so any path that is not a real file redirects to the root (a bookmarked path from the
previous site, or a path a proxy rewrites, then lands on the app instead of a 404), and the
build changes asset file names on every run, so responses carry no-cache headers to keep a
browser from holding an index.html that names assets which no longer exist.

Usage: python3 site/serve.py [--port 4002] [--bind 127.0.0.1] [--dir /tmp/site-output]
"""

import argparse
import functools
import http.server
import os
import subprocess
import sys


class Handler(http.server.SimpleHTTPRequestHandler):
    def end_headers(self):
        self.send_header("Cache-Control", "no-cache, must-revalidate")
        super().end_headers()

    def send_head(self):
        path = self.translate_path(self.path)
        if not os.path.exists(path):
            # Unknown path: send the browser to the app's entry page. The page loads its assets
            # by relative path, so it must be served at the root rather than in place.
            # The reader maps legacy chapter and map hash routes after the redirect.
            self.send_response(302)
            self.send_header("Location", "/")
            self.end_headers()
            return None
        return super().send_head()

    def log_message(self, fmt, *args):
        sys.stderr.write("%s %s\n" % (self.address_string(), fmt % args))


def main():
    parser = argparse.ArgumentParser(description=__doc__.split("\n")[0])
    parser.add_argument("--port", type=int, default=4002)
    parser.add_argument("--bind", default="127.0.0.1")
    root = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
    parser.add_argument("--dir", default=None)
    args = parser.parse_args()
    if args.dir is None:
        # Match build.sh's per-checkout default and environment overrides.
        args.dir = os.environ.get("OUT_DIR") or subprocess.check_output(
            [
                "bash", "--noprofile", "--norc", "-c",
                'source "$1/tests/lib/lake.sh"; printf "%s-site" "$FLOATLIB_BUILD_DIR"',
                "floatlib-preview", root,
            ],
            text=True,
        )
    if not os.path.isfile(os.path.join(args.dir, "index.html")):
        sys.exit(f"serve: no index.html under {args.dir}; run site/build.sh first")
    handler = functools.partial(Handler, directory=args.dir)
    with http.server.ThreadingHTTPServer((args.bind, args.port), handler) as server:
        print(f"serving {args.dir} at http://127.0.0.1:{args.port}/", flush=True)
        server.serve_forever()


if __name__ == "__main__":
    main()
