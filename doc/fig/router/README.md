# Border router operation diagrams

Six slide-sized diagrams describing the high-level operation of the SCION border
router as implemented in `router/dataplane.go`, `router/control` and
`router/cmd/router`. Every figure is 1600×900 (16:9).

| Figure | Shows |
| --- | --- |
| `01-router-overview` | The router as a crossbar: one socket per interface, one shared per-packet pipeline, and the four traffic patterns (inbound, outbound, BR transit, AS transit). |
| `02-router-startup` | Configuration from `topology.json` through `control.IACtx.Configure()` into the `DataPlane`, then `Run()` spawning one receive goroutine per interface plus the BFD sessions. |
| `03-router-forwarding-loop` | The `read(ingressID, conn)` closure: `ReadBatch` of up to 64 packets, per-packet counters, `processPkt`, error classification, non-blocking `WriteBatch`. |
| `04-router-parse-dispatch` | `processPkt()`: `reset()`, `decodeLayers()` over the SCION header and the extension-header skippers, then the dispatch on `PathType` (BFD / one-hop / SCION / EPIC). |
| `05-router-ingress-checks` | The nine ordered ingress checks in `process()`, each with the SCMP error or silent drop it produces. |
| `06-router-egress-decision` | The forwarding decision: local delivery, cross-over and egress-link validation, and the three egress outcomes. |

Each figure ships as:

* `NN-*.svg` — vector, and the source of truth. PowerPoint, Keynote and Google
  Slides all import it; PowerPoint can convert it to editable shapes with
  *Graphics Format → Convert to Shape*.
* `NN-*.png` — 3200×1800 raster, for tools that do not take SVG.

`scion-router-operations.pptx` holds all six as full-bleed 16:9 slides with
speaker notes, so individual slides can be copied into an existing deck.

## Regenerating

```sh
python3 doc/fig/router/gen_diagrams.py   # SVG
python3 doc/fig/router/render_png.py     # PNG, needs Pillow and Chromium
node    doc/fig/router/make_deck.js      # PPTX, needs pptxgenjs
```

`gen_diagrams.py` has no dependencies. `render_png.py` needs `Pillow` and the
Chromium binary path set at the top of the file. `make_deck.js` needs
`pptxgenjs` on `NODE_PATH`.

The diagrams are hand-laid-out, so a change to the code they describe means
editing the corresponding `dNN_*()` function rather than re-running a layout
engine.
