#!/usr/bin/env python3
"""Render every 0*.svg in this directory to a 2x PNG using headless Chromium.

Chromium clips the last rows when the window height exactly matches the SVG,
so the page is rendered into an oversized window and cropped afterwards.

    python3 doc/fig/router/render_png.py
"""

import glob
import os
import subprocess
import tempfile

from PIL import Image

OUT = os.path.dirname(os.path.abspath(__file__))
CHROME = "/opt/pw-browsers/chromium-1194/chrome-linux/chrome"
W, H, SCALE = 1600, 900, 2

WRAPPER = """<!doctype html><meta charset="utf-8">
<style>html,body{{margin:0;padding:0;background:#fff}}
svg{{display:block;width:{w}px;height:{h}px}}</style>
{svg}
"""


def main():
    tmp = tempfile.mkdtemp()
    for src in sorted(glob.glob(os.path.join(OUT, "0*.svg"))):
        base = os.path.splitext(os.path.basename(src))[0]
        page = os.path.join(tmp, base + ".html")
        with open(page, "w", encoding="utf-8") as fh:
            fh.write(WRAPPER.format(w=W, h=H, svg=open(src, encoding="utf-8").read()))
        shot = os.path.join(tmp, base + ".png")
        subprocess.run(
            [CHROME, "--headless", "--disable-gpu", "--no-sandbox", "--hide-scrollbars",
             f"--force-device-scale-factor={SCALE}",
             f"--window-size={W + 120},{H + 120}",
             f"--screenshot={shot}", "file://" + page],
            check=True, capture_output=True,
        )
        dst = os.path.join(OUT, base + ".png")
        Image.open(shot).crop((0, 0, W * SCALE, H * SCALE)).save(dst)
        print("wrote", os.path.relpath(dst), f"{W * SCALE}x{H * SCALE}")


if __name__ == "__main__":
    main()
