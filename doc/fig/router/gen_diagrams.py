#!/usr/bin/env python3
"""Generate the border-router operation diagrams in doc/fig/router.

The diagrams describe the high-level operation of the SCION border router as it
is implemented in router/dataplane.go, router/control and router/cmd/router.

Every diagram is a self-contained SVG sized 1600x900 (16:9), drawn with plain
shapes and presentation attributes only, so that PowerPoint / Keynote / Google
Slides can import it and convert it into editable shapes.

    python3 doc/fig/router/gen_diagrams.py
"""

import math
import os

OUT = os.path.dirname(os.path.abspath(__file__))

W, H = 1600, 900

SANS = "Segoe UI, Arial, Helvetica, sans-serif"
MONO = "Consolas, DejaVu Sans Mono, Menlo, monospace"

BG = "#ffffff"
INK = "#12203a"
MUTED = "#5b6b85"
LINE = "#8fa0b8"
REDTX = "#a51c1c"

# palette entries: (fill, stroke, title colour)
NEU = ("#f3f6fa", "#c3cedd", INK)
SLA = ("#e8edf4", "#9aabc2", INK)
BLU = ("#dbeafe", "#2563eb", INK)
AMB = ("#fef3c7", "#d97706", INK)
RED = ("#fee2e2", "#dc2626", REDTX)
GRN = ("#dcfce7", "#16a34a", "#0f3d22")
PUR = ("#ede9fe", "#7c3aed", INK)
TEA = ("#ccfbf1", "#0d9488", "#0b3b36")

C_GRN, C_BLU, C_PUR, C_ORG = "#16a34a", "#2563eb", "#7c3aed", "#ea580c"


def esc(s):
    return s.replace("&", "&amp;").replace("<", "&lt;").replace(">", "&gt;")


def r(v):
    return f"{v:.1f}".rstrip("0").rstrip(".")


def T(s, x, y, size=12.5, fill=INK, anchor="start", weight="400", family=SANS):
    # xml:space="preserve" keeps the runs of spaces that align the monospaced
    # columns inside the code-like boxes.
    return (
        f'<text x="{r(x)}" y="{r(y)}" font-family="{family}" font-size="{r(size)}" '
        f'fill="{fill}" text-anchor="{anchor}" font-weight="{weight}" '
        f'xml:space="preserve">{esc(s)}</text>'
    )


def rect(x, y, w, h, fill, stroke=None, rx=0, sw=1.6, dash=None):
    s = f'<rect x="{r(x)}" y="{r(y)}" width="{r(w)}" height="{r(h)}" rx="{r(rx)}" fill="{fill}"'
    if stroke:
        s += f' stroke="{stroke}" stroke-width="{r(sw)}"'
    if dash:
        s += f' stroke-dasharray="{dash}"'
    return s + "/>"


def line(x1, y1, x2, y2, color=LINE, sw=1.4, dash=None):
    s = (
        f'<line x1="{r(x1)}" y1="{r(y1)}" x2="{r(x2)}" y2="{r(y2)}" '
        f'stroke="{color}" stroke-width="{r(sw)}"'
    )
    if dash:
        s += f' stroke-dasharray="{dash}"'
    return s + "/>"


def arrow(pts, color=LINE, sw=2.0, dash=None, head=True, hs=9.0):
    """Polyline with an explicit triangular arrowhead (markers are unreliable
    in PowerPoint's SVG importer)."""
    pts = [(float(a), float(b)) for a, b in pts]
    out = []
    if head and len(pts) >= 2:
        (x1, y1), (x2, y2) = pts[-2], pts[-1]
        ang = math.atan2(y2 - y1, x2 - x1)
        bx, by = x2 - hs * math.cos(ang), y2 - hs * math.sin(ang)
        pts = pts[:-1] + [(bx, by)]
        p1 = (x2, y2)
        p2 = (bx - hs * 0.45 * math.sin(-ang), by - hs * 0.45 * math.cos(-ang))
        p3 = (bx + hs * 0.45 * math.sin(-ang), by + hs * 0.45 * math.cos(-ang))
        tri = " ".join(f"{r(a)},{r(b)}" for a, b in (p1, p2, p3))
        out.append(f'<polygon points="{tri}" fill="{color}"/>')
    d = " ".join(f"{r(a)},{r(b)}" for a, b in pts)
    s = (
        f'<polyline points="{d}" fill="none" stroke="{color}" stroke-width="{r(sw)}" '
        f'stroke-linejoin="round" stroke-linecap="round"'
    )
    if dash:
        s += f' stroke-dasharray="{dash}"'
    return [s + "/>"] + out


class Svg:
    def __init__(self, w=W, h=H, bg=BG):
        self.w, self.h, self.p = w, h, []
        if bg:
            self.p.append(rect(0, 0, w, h, bg))

    def add(self, *items):
        for it in items:
            if isinstance(it, list):
                self.p.extend(it)
            else:
                self.p.append(it)

    def head(self, title, sub):
        self.add(T(title, 70, 52, 26, INK, weight="700"))
        self.add(T(sub, 70, 80, 14, MUTED))
        self.add(line(70, 96, self.w - 70, 96, "#d7dfea", 1.4))

    def box(self, x, y, w, h, title="", sub=None, lines=None, alt=None, note=None,
            pal=NEU, rx=10, ts=15, ls=12.5, pad=13, center=False, dash=None,
            tmono=True, lmono=False, sw=1.6, lead=1.46, tfill=None,
            lfill=MUTED, subfill=MUTED, ss=12.0):
        fill, stroke, tc = pal
        self.add(rect(x, y, w, h, fill, stroke, rx, sw, dash))
        tx = x + w / 2 if center else x + pad
        anch = "middle" if center else "start"
        by = y + pad + ts * 0.84
        if title:
            self.add(T(title, tx, by, ts, tfill or tc, anch, "700",
                       MONO if tmono else SANS))
        if sub:
            by += ss * 1.42
            self.add(T(sub, tx, by, ss, subfill, anch, "400", SANS))
        if lines:
            by += ls * 1.62
            for i, ln in enumerate(lines):
                if ln:
                    self.add(T(ln, tx, by + i * ls * lead, ls, lfill, anch, "400",
                               MONO if lmono else SANS))
        for block, colour, rule in ((alt, REDTX, "#e9b7b7"), (note, MUTED, "#cfd8e4")):
            if not block:
                continue
            blk = len(block) * ls * lead
            top = y + h - pad - blk + 2
            self.add(line(x + pad, top, x + w - pad, top, rule, 1.2))
            for i, ln in enumerate(block):
                self.add(T(ln, tx, top + 8 + ls + i * ls * lead, ls, colour, anch,
                           "400", SANS))

    def chip(self, x, y, w, h, text, pal=NEU, rx=8, size=13, mono=True,
             weight="700", dash=None, sub=None):
        fill, stroke, tc = pal
        self.add(rect(x, y, w, h, fill, stroke, rx, 1.5, dash))
        cy = y + h / 2 + (size * 0.35 if not sub else -1)
        self.add(T(text, x + w / 2, cy, size, tc, "middle", weight,
                   MONO if mono else SANS))
        if sub:
            self.add(T(sub, x + w / 2, cy + 16, 11.5, MUTED, "middle", "400", SANS))

    def render(self, title, desc):
        body = "\n  ".join(self.p)
        return (
            f'<svg xmlns="http://www.w3.org/2000/svg" viewBox="0 0 {self.w} {self.h}" '
            f'width="{self.w}" height="{self.h}" role="img" aria-label="{esc(desc)}">\n'
            f"  <title>{esc(title)}</title>\n  <desc>{esc(desc)}</desc>\n  {body}\n</svg>\n"
        )


def write(name, svg, title, desc):
    path = os.path.join(OUT, name)
    with open(path, "w", encoding="utf-8") as fh:
        fh.write(svg.render(title, desc))
    print("wrote", os.path.relpath(path))


# ---------------------------------------------------------------- diagram 1


def d01_overview():
    g = Svg()
    g.head(
        "The SCION border router at a glance",
        "One process per border router, one UDP/IP socket per interface. Every packet enters on one "
        "interface, is validated, and leaves on the interface named by its hop field.",
    )

    g.add(rect(250, 132, 1100, 480, "#fbfcfe", "#c3cedd", 16, 1.8))
    g.add(T("border router process  ·  router/cmd/router → router.DataPlane",
            800, 160, 14.5, INK, "middle", "700"))

    g.add(T("ingress", 415, 205, 12, MUTED, "middle", "700"))
    g.add(T("egress", 1185, 205, 12, MUTED, "middle", "700"))

    ext = [("ext ifID 1", "socket to a neighbour AS", 250),
           ("ext ifID 2", "socket to a neighbour AS", 340)]
    intern = ("internal ifID 0", "socket inside the local AS", 470)

    for lbl, sub, y in ext + [intern]:
        pal = BLU if lbl.startswith("ext") else TEA
        g.chip(290, y, 250, 54, lbl, pal, 8, 14, True, "700", sub=sub)
        g.chip(1060, y, 250, 54, lbl, pal, 8, 14, True, "700", sub=sub)

    # the shared per-packet pipeline
    g.add(rect(690, 218, 220, 356, BLU[0], BLU[1], 14, 1.8))
    g.add(T("processPkt()", 800, 250, 15.5, INK, "middle", "700", MONO))
    g.add(T("→ process()", 800, 272, 13.5, MUTED, "middle", "400", MONO))
    g.add(line(706, 288, 894, 288, "#9dbcf2", 1.2))
    g.add(T("one goroutine", 800, 538, 11.5, MUTED, "middle"))
    g.add(T("per ingress interface", 800, 554, 11.5, MUTED, "middle"))

    flows = [
        ((540, 271), (1060, 491), C_GRN),   # inbound   ext1 -> internal
        ((540, 283), (1060, 355), C_PUR),   # BR transit ext1 -> ext2
        ((540, 379), (1060, 503), C_ORG),   # AS transit ext2 -> internal
        ((540, 491), (1060, 367), C_BLU),   # outbound  internal -> ext2
    ]
    for (sx, sy), (ex, ey), col in flows:
        g.add(arrow([(sx, sy), (700, sy), (890, ey), (ex, ey)], col, 2.4, hs=10))

    # the world around the router
    ctx = [(40, 250, "Neighbour AS", "1-ff00:0:110 (parent link)"),
           (40, 340, "Neighbour AS", "1-ff00:0:112 (child link)"),
           (40, 470, "Local AS", "end hosts · sibling BRs · CS")]
    for x, y, a, b in ctx:
        g.chip(x, y, 190, 54, a, NEU, 8, 13, False, "700", sub=b)
        g.chip(1370, y, 190, 54, a, NEU, 8, 13, False, "700", sub=b)
        g.add(arrow([(230, y + 27), (288, y + 27)], LINE, 1.8, hs=8))
        g.add(arrow([(1312, y + 27), (1368, y + 27)], LINE, 1.8, hs=8))

    # the four traffic patterns
    g.add(T("four traffic patterns — process() picks the route through the crossbar",
            70, 664, 15, INK, weight="700"))
    rows = [
        (C_GRN, "Inbound", "ext ifID N → internal ifID 0 → end host",
         "DstIA == d.localIA  →  resolveInbound() → resolveLocalDst()"),
        (C_BLU, "Outbound", "internal ifID 0 → ext ifID N",
         "ingressID == 0  and  egressID in d.external  → processEgress()"),
        (C_PUR, "BR transit", "ext ifID A → ext ifID B",
         "egressID in d.external  → processEgress(): UpdateSegID + IncPath"),
        (C_ORG, "AS transit", "ext ifID N → internal ifID 0 → sibling BR",
         "egressID in d.internalNextHops  — the path is not advanced here"),
    ]
    y = 690
    g.add(line(70, y, 1530, y, "#d7dfea", 1.2))
    for col, name, route, decision in rows:
        y += 44
        g.add(rect(70, y - 22, 30, 11, col, None, 3))
        g.add(T(name, 116, y - 12, 14, INK, weight="700"))
        g.add(T(route, 250, y - 12, 12.5, INK, family=MONO))
        g.add(T(decision, 700, y - 12, 12.5, MUTED, family=MONO))
        g.add(line(70, y, 1530, y, "#e6ebf2", 1))

    write("01-router-overview.svg", g,
          "SCION border router at a glance",
          "Crossbar view of a SCION border router: external and internal interfaces feed a single "
          "per-packet pipeline, which routes inbound, outbound, BR transit and AS transit traffic.")


# ---------------------------------------------------------------- diagram 2


def d02_startup():
    g = Svg()
    g.head(
        "Startup: configure the DataPlane, then Run() spawns one receive loop per interface",
        "router/cmd/router/main.go  ·  router/control  ·  router/dataplane.go",
    )

    g.box(50, 130, 250, 96, "main() → realMain(ctx)",
          lines=["router/cmd/router/main.go", "an errgroup owns every", "long-running task"],
          pal=NEU, ts=14, ls=11.5)
    g.add(arrow([(300, 178), (338, 178)], LINE, 2))

    g.box(340, 130, 300, 118, "control.LoadConfig(id, confDir)",
          lines=["topology.json → interfaces,", "  neighbours, link types,",
                 "  sibling BRs, services",
                 "keys/master0.key → DeriveHFMacKey"],
          pal=NEU, ts=13.5, ls=11.5)
    g.add(arrow([(640, 178), (678, 178)], LINE, 2))

    g.box(680, 130, 300, 220, "control.IACtx.Configure()",
          sub="ConfigDataplane(dp, cfg) calls, in order:",
          lines=["SetIA(ia)", "SetKey(masterKey)",
                 "AddInternalInterface(conn, ip)", "AddExternalInterface(ifID, conn)",
                 "AddNeighborIA(ifID, ia)", "AddLinkType(ifID, linkTo)",
                 "AddNextHop(ifID, siblingBR)", "AddSvc(svc, addr)",
                 "AddExternalInterfaceBFD(...)", "AddNextHopBFD(...)"],
          pal=AMB, ts=14, ls=11.5, lmono=True, lfill=INK, lead=1.4)
    g.add(arrow([(980, 178), (1018, 178)], LINE, 2))

    g.box(1020, 130, 530, 244, "DataPlane — the forwarding state",
          sub="d.mtx guards it; every setter refuses to run once d.running is true",
          lines=["external          map[uint16]BatchConn",
                 "internal          BatchConn",
                 "internalNextHops  map[uint16]*net.UDPAddr",
                 "neighborIAs       map[uint16]addr.IA",
                 "linkTypes         map[uint16]topology.LinkType",
                 "svc               *services",
                 "macFactory        func() hash.Hash",
                 "bfdSessions       map[uint16]bfdSession",
                 "localIA, internalIP, running",
                 "forwardingMetrics map[uint16]forwardingMetrics"],
          pal=BLU, ts=15, ls=12, lmono=True, lfill=INK, tmono=False, lead=1.42)

    # rail: configuration finished -> Run
    g.add(arrow([(1285, 374), (1285, 442), (255, 442), (255, 482)], LINE, 2.2))
    g.add(T("configuration complete → DataPlane.Run(ctx)", 770, 434, 12.5, MUTED, "middle"))

    g.box(50, 482, 420, 250, "DataPlane.Run(ctx)",
          sub="router/dataplane.go",
          lines=["d.mtx.Lock(); d.running = true",
                 "d.initMetrics()",
                 "spawn the goroutines →",
                 "d.mtx.Unlock()",
                 "<-ctx.Done()   // park until shutdown"],
          note=["Run() never touches a packet itself — it only starts",
                "the loops and then blocks until the context is cancelled."],
          pal=GRN, ts=17, ls=12.5, lmono=True, lfill=INK, lead=1.7)

    g.add(T("goroutines started by Run()", 530, 508, 14, INK, weight="700"))
    lanes = [
        (530, "go read(ifID, d.external[ifID])", "one per external interface · packets from a neighbour AS", PUR),
        (634, "go read(0, d.internal)", "exactly one · packets from inside the local AS", PUR),
        (738, "go bfdSession.Run(ctx)", "one per BFD session · liveness of links and sibling BRs", TEA),
    ]
    for y, title, sub, pal in lanes:
        g.box(530, y, 500, 84, title, sub=sub, pal=pal, ts=14, ss=11.5)
    g.add(arrow([(470, 572), (530, 572)], "#7c3aed", 2))
    g.add(arrow([(470, 632), (500, 632), (500, 676), (530, 676)], "#7c3aed", 2))
    g.add(arrow([(470, 692), (500, 692), (500, 780), (530, 780)], "#0d9488", 2))

    g.add(rect(1058, 496, 492, 330, "#fbfcfe", "#c3cedd", 12, 1.4, "6 5"))
    g.add(T("also started by realMain()'s errgroup", 1070, 508, 14, INK, weight="700"))
    for y, title, sub in [
        (530, "go Metrics.ServePrometheus(ctx)", "scrape endpoint for the forwarding counters"),
        (634, "go mgmtServer.ListenAndServe()", "management API /api/v1: interfaces, config, log level"),
        (738, "go cleanup.Do()", "on ctx.Done(): close the management server"),
    ]:
        g.box(1070, y, 468, 84, title, sub=sub, pal=SLA, ts=13.5, ss=11.5)

    g.add(T("Each read goroutine owns 64 receive buffers of 9000 B and one scionPacketProcessor, "
            "so the packet path allocates nothing.", 530, 858, 13, MUTED))

    write("02-router-startup.svg", g,
          "Border router startup and goroutines",
          "Configuration flows from topology.json through control.IACtx.Configure into the DataPlane "
          "forwarding state; Run then spawns one read goroutine per interface plus the BFD sessions.")


# ---------------------------------------------------------------- diagram 3


def d03_loop():
    g = Svg()
    g.head(
        "read(ingressID, conn): the receive → process → send loop",
        "The closure that Run() spawns once per interface. All the loops run concurrently and share "
        "the read-only DataPlane.",
    )

    g.add(rect(70, 112, 1460, 52, SLA[0], SLA[1], 9, 1.5))
    g.add(T("allocated once, before the loop:   msgs := 64 × 9000 B buffers "
            "(inputBatchCnt × bufSize)   ·   writeMsgs   ·   "
            "processor := newPacketProcessor(d, ingressID)",
            800, 144, 13, INK, "middle", "400", MONO))

    # ---- column 1
    g.chip(70, 188, 660, 44, "for d.running {", NEU, 8, 15, True, "700", dash="6 5")

    g.box(70, 252, 660, 100, "pkts, err := rd.ReadBatch(msgs)",
          lines=["one syscall receives up to 64 packets into the pre-allocated buffers"],
          alt=["err != nil → log.Debug(\"Failed to read batch\")   ·   "
               "pkts == 0   → next batch"],
          pal=BLU, ts=15.5)
    g.add(arrow([(400, 232), (400, 250)], LINE, 2))

    g.chip(70, 380, 660, 44, "for i := 0; i < pkts; i++ {", NEU, 8, 15, True, "700", dash="6 5")
    g.add(arrow([(400, 352), (400, 378)], LINE, 2))

    g.box(70, 448, 660, 76, "input counters",
          lines=["InputPacketsTotal++   ·   InputBytesTotal += p.N",
                 "labelled with the ingress interface"],
          pal=SLA, ts=14, tmono=False, ls=12)
    g.add(arrow([(400, 424), (400, 446)], LINE, 2))

    g.box(70, 552, 660, 196, "result, err := processor.processPkt(rawPkt, srcAddr)",
          lines=["rawPkt  = p.Buffers[0][:p.N]",
                 "srcAddr = p.Addr.(*net.UDPAddr)",
                 "",
                 "the same scionPacketProcessor is reused for every packet on this",
                 "interface, so parsing allocates nothing",
                 "",
                 "→ parsing and dispatch: diagram 4"],
          pal=BLU, ts=14.5, ls=12)
    g.add(arrow([(400, 524), (400, 550)], LINE, 2))

    # rail across to column 2
    g.add(arrow([(400, 748), (400, 782), (800, 782), (800, 208), (866, 208)], LINE, 2.2))
    g.add(T("result, err", 812, 470, 12.5, MUTED))

    # ---- column 2
    g.box(870, 180, 660, 164, "classify err",
          lines=["err == nil                 forward exactly as result says",
                 "errors.As(err, &scmpErr)   OutAddr = srcAddr; OutConn = rd",
                 "                           an SCMP reply goes back the way",
                 "                           the packet came in"],
          alt=["any other error → log.Debug, DroppedPacketsTotal++, next packet"],
          pal=AMB, ts=15, ls=12, lmono=True, lfill=INK)

    g.box(870, 376, 660, 80, "result.OutConn == nil ?",
          lines=["a BFD packet was consumed by its session — nothing to send, next packet"],
          pal=TEA, ts=15, ls=12)
    g.add(arrow([(1200, 344), (1200, 374)], LINE, 2))

    g.box(870, 488, 660, 140, "result.OutConn.WriteBatch(writeMsgs, syscall.MSG_DONTWAIT)",
          lines=["writeMsgs[0].Buffers[0] = result.OutPkt",
                 "writeMsgs[0].Addr       = result.OutAddr   (nil on a connected socket)"],
          alt=["EAGAIN / EWOULDBLOCK → drop the packet.",
               "The forwarding loop must never block on a send."],
          pal=BLU, ts=13.5, ls=12, lmono=True, lfill=INK)
    g.add(arrow([(1200, 456), (1200, 486)], LINE, 2))

    g.box(870, 660, 660, 76, "output counters",
          lines=["OutputPacketsTotal++   ·   OutputBytesTotal += len(result.OutPkt)",
                 "labelled with result.EgressID"],
          pal=GRN, ts=14, tmono=False, ls=12)
    g.add(arrow([(1200, 628), (1200, 658)], LINE, 2))

    g.add(arrow([(1200, 736), (1200, 806), (60, 806), (60, 402), (68, 402)], LINE, 2.2))
    g.add(T("next packet in the batch, then the next batch", 850, 798, 13, MUTED))

    g.add(rect(70, 830, 1460, 56, NEU[0], NEU[1], 9, 1.5))
    g.add(T("Concurrency: a goroutine reads only its own socket, but it may write to any other "
            "interface's socket — the packet is sent by the goroutine that received it.",
            88, 852, 12.5, INK))
    g.add(T("Every DataPlane map is read-only once d.running is true, so the packet path takes "
            "no lock at all.", 88, 872, 12.5, MUTED))

    write("03-router-forwarding-loop.svg", g,
          "Border router forwarding loop",
          "The per-interface read loop: ReadBatch of up to 64 packets, per-packet counters, "
          "processPkt, error classification, non-blocking WriteBatch and output counters.")


# ---------------------------------------------------------------- diagram 4


def d04_parse():
    g = Svg()
    g.head(
        "processPkt(): reset, parse the headers, dispatch on the path type",
        "decodeLayers() decodes the SCION header and then skips the hop-by-hop and end-to-end "
        "extension headers; the path type in the common header selects the handler.",
    )

    segs = [
        (70, 250, "SCION common hdr", "NextHdr · HdrLen · PayloadLen · PathType", BLU),
        (322, 258, "address header", "DstIA · SrcIA · DstAddr · SrcAddr", BLU),
        (582, 300, "path", "empty | scion.Raw | onehop | epic", AMB),
        (884, 160, "HBH extn", "skipped", SLA),
        (1046, 160, "E2E extn", "skipped", SLA),
        (1208, 322, "payload", "L4 · SCMP · BFD", NEU),
    ]
    for x, w, a, b, pal in segs:
        g.add(rect(x, 114, w, 62, pal[0], pal[1], 6, 1.5))
        g.add(T(a, x + w / 2, 138, 13.5, INK, "middle", "700"))
        g.add(T(b, x + w / 2, 158, 11, MUTED, "middle"))
    g.add(T("wire format, as parsed by decodeLayers(rawPkt, &p.scionLayer, &p.hbhLayer, &p.e2eLayer)"
            "   —   pld := lastLayer.LayerPayload()",
            70, 196, 12.5, MUTED, family=MONO))

    g.box(70, 228, 300, 100, "p.reset()",
          lines=["clears rawPkt, path, hopField,", "infoField, segmentChange, the",
                 "serialize buffer and the MAC"],
          pal=SLA, ts=15, ls=11.5)
    g.add(arrow([(370, 278), (408, 278)], LINE, 2))

    g.box(410, 228, 470, 100, "decodeLayers(rawPkt, ...)",
          lines=["SCION header → HBH skipper → E2E skipper",
                 "keeps lastLayer and its payload"],
          alt=["a decode error ends the packet: dropped, no SCMP"],
          pal=BLU, ts=15, ls=12)
    g.add(arrow([(880, 278), (918, 278)], LINE, 2))

    g.box(920, 228, 610, 100, "switch p.scionLayer.PathType",
          lines=["the empty and onehop cases also test",
                 "lastLayer.NextLayerType() == LayerTypeBFD"],
          pal=AMB, ts=15, ls=12)

    cols = [
        (70, 290, "empty  (0)", TEA, TEA,
         ["next layer is BFD?", ""],
         "p.processIntraBFD(pld)",
         ["match srcAddr against",
          "d.internalNextHops to find ifID",
          "→ d.bfdSessions[ifID]",
          "      .ReceiveMessage(bfd)",
          "",
          "any other next header:",
          "unsupportedPathTypeNextHeader"],
         "consumed · OutConn == nil", TEA),
        (380, 310, "onehop  (2)", AMB, AMB,
         ["next layer is BFD?", ""],
         "processInterBFD / processOHP",
         ["BFD → d.bfdSessions[ingressID]",
          "          .ReceiveMessage(bfd)",
          "",
          "otherwise p.processOHP()  (beaconing)",
          "ingress 0: check SrcIA and the",
          "   neighbour, verify the FirstHop MAC,",
          "   UpdateSegID, send on",
          "   d.external[ConsEgress]",
          "ingress != 0: fill SecondHop",
          "   {ConsIngress, ExpTime}, compute its",
          "   MAC, then deliver inside the AS"],
         "forwarded, or consumed by BFD", GRN),
        (710, 290, "scion  (1)", BLU, BLU,
         ["the common case", ""],
         "p.processSCION()",
         ["p.path = scionLayer.Path.(*scion.Raw)",
          "not a *scion.Raw → malformedPath",
          "",
          "→ p.process()",
          "the validation chain and the egress",
          "decision: diagrams 5 and 6"],
         "processResult → forwarded", GRN),
        (1020, 280, "epic  (3)", PUR, PUR,
         ["scion path plus EPIC hop validators", ""],
         "p.processEPIC()",
         ["p.path = epicPath.ScionPath",
          "→ p.process()   (the same chain)",
          "",
          "then, only on the penultimate and",
          "the last hop:",
          "  libepic.VerifyTimestamp(...)",
          "  libepic.VerifyHVF(p.cachedMac,",
          "     PktID, PHVF | LHVF)",
          "reusing the MAC that",
          "verifyCurrentMAC already computed"],
         "processResult → forwarded", GRN),
        (1320, 210, "default", RED, RED,
         ["", ""],
         "unsupportedPathType",
         ["the path type is not one the", "router knows how to forward"],
         "dropped", RED),
    ]

    g.add(arrow([(1225, 328), (1225, 352)], LINE, 2))
    g.add(line(220, 352, 1450, 352, LINE, 2))
    for x, w, case, cpal, hpal, _sub, htitle, hlines, out, opal in cols:
        cx = x + w / 2
        g.add(arrow([(cx, 352), (cx, 378)], LINE, 2))
        g.chip(x, 380, w, 44, case, cpal, 8, 15)
        g.box(x, 444, w, 278, htitle, lines=hlines, pal=hpal, ts=13.5, ls=11.5, lead=1.5)
        g.chip(x, 738, w, 54, out, opal, 8, 12.5, mono=False)

    g.add(line(70, 820, 1530, 820, "#d7dfea", 1.2))
    g.add(T("Every branch returns processResult{ EgressID, OutConn, OutAddr, OutPkt } to the "
            "forwarding loop; an empty OutConn means the packet was consumed here.",
            800, 848, 13, MUTED, "middle"))

    write("04-router-parse-dispatch.svg", g,
          "processPkt parsing and dispatch",
          "processPkt resets the reusable processor, decodes the SCION header and extension headers, "
          "and dispatches on the path type to the BFD, one-hop, SCION or EPIC handler.")


# ---------------------------------------------------------------- diagram 5


def d05_ingress():
    g = Svg()
    g.head(
        "process(): the ingress checks, in order",
        "Each step either returns cleanly and the chain continues, or it ends the packet — with an "
        "SCMP error built by packSCMP(), or with a silent drop.",
    )

    steps = [
        ("parsePath()",
         "read CurrINF / CurrHF and load p.hopField and p.infoField from the raw path",
         RED, "malformedPath — dropped, no SCMP"),
        ("validateHopExpiry()",
         "the hop field's ExpTime, relative to the info field timestamp, against now",
         RED, "SCMP ParameterProblem / PathExpired"),
        ("validateIngressID()",
         "the hop field's ConsIngress (ConsEgress against construction direction) must be "
         "the interface the packet arrived on",
         RED, "SCMP ParameterProblem / UnknownHopFieldIngress | UnknownHopFieldEgress"),
        ("validatePktLen()",
         "the SCION PayloadLen must match the number of bytes actually received",
         RED, "SCMP ParameterProblem / InvalidPacketSize"),
        ("validateTransitUnderlaySrc()",
         "a transit packet arriving on the internal interface must come from the sibling BR "
         "that owns the packet's ingress interface",
         RED, "invalidSrcAddrForTransit — dropped, no SCMP"),
        ("validateSrcDstIA()",
         "outbound: the first hop must have a local SrcIA and DstIA must not be local; "
         "inbound: SrcIA must not be local, and IsLastHop() must agree with a local DstIA",
         RED, "SCMP ParameterProblem / InvalidSourceAddress | InvalidDestinationAddress"),
        ("updateNonConsDirIngressSegID()",
         "against construction direction, and not from inside the AS: SegID is updated with the "
         "current hop field's MAC before it is checked",
         SLA, "no failure path — it only rewrites the info field"),
        ("verifyCurrentMAC()",
         "AES-CMAC over the info field and the hop field with the AS hop-field key, compared in "
         "constant time; the full MAC is cached for EPIC",
         RED, "SCMP ParameterProblem / InvalidHopFieldMAC"),
        ("handleIngressRouterAlert()",
         "if the ingress router-alert flag is set for this direction: clear it and answer",
         BLU, "SCMP traceroute reply, returned to srcAddr"),
    ]

    g.add(T("in order", 52, 118, 11, MUTED, "middle"))
    g.add(arrow([(52, 128), (52, 806)], LINE, 2))

    y = 128
    for i, (name, desc, opal, outcome) in enumerate(steps):
        h = 64
        g.add(rect(70, y, 750, h, NEU[0], NEU[1], 9, 1.5))
        g.add(line(52, y + h / 2, 68, y + h / 2, LINE, 1.4))
        g.add(f'<circle cx="96" cy="{r(y + h / 2)}" r="13" fill="{opal[1]}"/>')
        g.add(T(str(i + 1), 96, y + h / 2 + 4.5, 13, "#ffffff", "middle", "700"))
        g.add(T(name, 122, y + 26, 14.5, INK, weight="700", family=MONO))
        # description, wrapped to at most two lines
        words, cur, out = desc.split(), "", []
        for wd in words:
            t = (cur + " " + wd).strip()
            if len(t) > 84 and cur:
                out.append(cur)
                cur = wd
            else:
                cur = t
        out.append(cur)
        for j, ln in enumerate(out[:2]):
            g.add(T(ln, 122, y + 44 + j * 15, 11.8, MUTED))
        g.add(arrow([(820, y + h / 2), (856, y + h / 2)], opal[1], 1.8, hs=8))
        g.add(rect(860, y, 670, h, opal[0], opal[1], 9, 1.5))
        g.add(T("ends the packet" if opal is RED else
                ("continues" if opal is SLA else "answered here"),
                878, y + 24, 11, opal[2], weight="700"))
        g.add(T(outcome, 878, y + 45, 12.5, opal[2]))
        y += 78

    g.add(rect(70, 836, 1460, 50, GRN[0], GRN[1], 9, 1.6))
    g.add(T("all nine checks passed  →  where does the packet go?  (diagram 6)",
            800, 867, 15, GRN[2], "middle", "700"))

    write("05-router-ingress-checks.svg", g,
          "process(): ingress validation chain",
          "The nine ordered ingress checks in process(), each with the SCMP error or the silent drop "
          "it produces on failure.")


# ---------------------------------------------------------------- diagram 6


def d06_egress():
    g = Svg()
    g.head(
        "process(): where the packet goes",
        "The destination ISD-AS decides local delivery; otherwise the hop field's egress interface "
        "decides which socket the packet leaves on.",
    )

    g.chip(560, 112, 480, 48, "the ingress checks passed", BLU, 9, 14.5, mono=False)
    g.add(arrow([(800, 160), (800, 190)], LINE, 2))
    g.chip(560, 190, 480, 60, "p.scionLayer.DstIA == p.d.localIA ?", AMB, 9, 16)

    g.add(arrow([(560, 220), (350, 220), (350, 268)], C_GRN, 2.4))
    g.add(T("yes", 470, 210, 13, C_GRN, "middle", "700"))
    g.add(arrow([(1040, 220), (1120, 220), (1120, 268)], LINE, 2.4))
    g.add(T("no", 1082, 210, 13, MUTED, "middle", "700"))

    g.box(70, 270, 570, 246, "Inbound — deliver inside this AS",
          sub="resolveInbound() → d.resolveLocalDst(&p.scionLayer)",
          lines=["a service address (CS, DS, ...):",
                 "    d.svc.Any(svc.Base()) picks a registered instance",
                 "a host address:",
                 "    the host IP plus the fixed end-host port (topology.EndhostPort)",
                 "",
                 "result = { OutConn: d.internal, OutAddr: host, OutPkt: p.rawPkt }",
                 "the path is not advanced — this router is the last hop"],
          alt=["no registered SVC backend → SCMP DestinationUnreachable / NoRoute"],
          pal=GRN, ts=16, tmono=False, ls=12, lmono=True, lfill=INK)

    g.box(70, 532, 570, 74, "how an SCMP error gets back",
          lines=["packSCMP() returns an scmpError; the forwarding loop then sets",
                 "OutAddr = srcAddr and OutConn = the ingress socket."],
          pal=NEU, ts=13.5, tmono=False, ls=12)

    g.box(700, 270, 830, 74, "p.path.IsXover() ?",
          lines=["yes → doXover(): move to the next path segment and set segmentChange, "
                 "then re-run validateHopExpiry and verifyCurrentMAC on the new hop field"],
          pal=AMB, ts=15, ls=12)

    g.box(700, 356, 830, 116, "validateEgressID()",
          sub="the (ingress link type → egress link type) pair must be allowed",
          lines=["inside one segment:  internal → external,  core → core,  "
                 "child → parent,  parent → child",
                 "across a segment switch:  core → child,  child → core,  child → child"],
          alt=["otherwise → SCMP ParameterProblem / InvalidPath or InvalidSegmentChange"],
          pal=AMB, ts=15, ls=12)

    g.box(700, 484, 830, 86, "handleEgressRouterAlert()   ·   validateEgressUp()",
          lines=["answer a traceroute aimed at the egress interface, then check its BFD session"],
          alt=["session down → SCMP ExternalInterfaceDown or InternalConnectivityDown"],
          pal=AMB, ts=15, ls=12)

    g.add(arrow([(1115, 344), (1115, 354)], LINE, 2))
    g.add(arrow([(1115, 472), (1115, 482)], LINE, 2))

    g.chip(700, 582, 830, 42, "egressID := p.egressInterface()", SLA, 8, 15)
    g.add(arrow([(1115, 570), (1115, 580)], LINE, 2))

    g.add(arrow([(1115, 624), (1115, 638)], LINE, 2))
    g.add(line(305, 638, 1295, 638, LINE, 2))
    outs = [
        (70, 470, GRN, "Outbound  ·  BR transit",
         "egressID is in d.external",
         ["processEgress():",
          "   if infoField.ConsDir → UpdateSegID(hopField.Mac)",
          "   p.path.IncPath()  — advance to the next hop field",
          "scion.Raw writes both back into p.rawPkt in place",
          "",
          "result = { EgressID: egressID,",
          "           OutConn:  d.external[egressID],",
          "           OutPkt:   p.rawPkt }"]),
        (565, 470, GRN, "AS transit",
         "egressID is in d.internalNextHops",
         ["the egress interface belongs to a sibling border",
          "router in this AS, so the packet crosses the AS",
          "on the internal network first",
          "",
          "result = { OutConn: d.internal,",
          "           OutAddr: the sibling BR's underlay addr,",
          "           OutPkt:  p.rawPkt }",
          "the path is not advanced — the sibling BR does it"]),
        (1060, 470, RED, "unknown egress interface",
         "in neither map",
         ["SCMP ParameterProblem with",
          "   UnknownHopFieldEgress   (ConsDir)",
          "   UnknownHopFieldIngress  (against ConsDir)",
          "cause: cannotRoute",
          "",
          "the packet is dropped and the SCMP error is",
          "returned to the sender"]),
    ]
    for x, w, pal, title, sub, lines in outs:
        g.add(arrow([(x + w / 2, 638), (x + w / 2, 660)], LINE, 2))
        g.box(x, 662, w, 208, title, sub=sub, lines=lines, pal=pal, ts=15.5,
              tmono=False, ls=11.8, lmono=True, lfill=INK, lead=1.5)

    write("06-router-egress-decision.svg", g,
          "process(): the forwarding decision",
          "After the ingress checks, process() delivers locally when DstIA is the local AS, otherwise "
          "it validates the cross-over and egress link and picks the external socket, the internal "
          "socket toward a sibling border router, or an SCMP error.")


if __name__ == "__main__":
    d01_overview()
    d02_startup()
    d03_loop()
    d04_parse()
    d05_ingress()
    d06_egress()
