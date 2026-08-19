// Build doc/fig/router/scion-router-operations.pptx: one full-bleed diagram per
// 16:9 slide, so the slides can be pasted straight into an existing deck.
//
//   node doc/fig/router/make_deck.js

const path = require("path");
const pptxgen = require("pptxgenjs");

const DIR = __dirname;

const SLIDES = [
  {
    file: "01-router-overview.png",
    notes:
      "One border router = one process. It opens one UDP/IP socket per external interface " +
      "plus one internal socket toward the local AS. Everything funnels through the same " +
      "per-packet pipeline, which then switches the packet onto an egress socket. The four " +
      "traffic patterns (inbound, outbound, BR transit, AS transit) are just four routes " +
      "through that crossbar, chosen by process().",
  },
  {
    file: "02-router-startup.png",
    notes:
      "Configuration is a one-off phase: topology.json and the master key are loaded, then " +
      "control.IACtx.Configure() drives a sequence of setters that populate the DataPlane. " +
      "Every setter refuses to run once d.running is true, so the forwarding state is " +
      "effectively immutable while packets are flowing. Run() then starts one read goroutine " +
      "per interface plus the BFD sessions, and blocks on ctx.Done().",
  },
  {
    file: "03-router-forwarding-loop.png",
    notes:
      "The hot loop. ReadBatch pulls up to 64 packets in one syscall into buffers allocated " +
      "before the loop started. Each packet goes through processPkt, the error is classified " +
      "(SCMP errors are turned around and sent back to the sender), and the result is written " +
      "with MSG_DONTWAIT so a slow output socket can never stall the receive loop.",
  },
  {
    file: "04-router-parse-dispatch.png",
    notes:
      "processPkt resets the reusable processor, then decodeLayers walks the SCION header and " +
      "skips the hop-by-hop and end-to-end extension headers. The path type in the common " +
      "header selects the handler: BFD control packets are consumed by their session, one-hop " +
      "paths take the beaconing route, and scion/epic paths go into the main process() chain.",
  },
  {
    file: "05-router-ingress-checks.png",
    notes:
      "Nine ordered checks. Note the ordering: cheap structural checks come first and the " +
      "AES-CMAC verification comes late, after expiry, ingress interface, length and ISD-AS " +
      "checks have already rejected the obvious garbage. Most failures produce a specific SCMP " +
      "error; two of them (malformed path, bad transit source) drop the packet silently.",
  },
  {
    file: "06-router-egress-decision.png",
    notes:
      "Two questions decide everything. Is the destination ISD-AS us? Then resolve the local " +
      "destination and hand the packet to the internal socket. Otherwise validate the " +
      "cross-over and the egress link, then look the egress interface up: in d.external it " +
      "goes straight out (and the path is advanced here); in d.internalNextHops it goes to a " +
      "sibling border router over the internal network, which advances the path instead.",
  },
];

const pres = new pptxgen();
pres.defineLayout({ name: "SCION16x9", width: 13.333, height: 7.5 });
pres.layout = "SCION16x9";
pres.author = "generated from doc/fig/router/gen_diagrams.py";
pres.title = "SCION border router — high-level operations";

for (const s of SLIDES) {
  const slide = pres.addSlide();
  slide.background = { color: "FFFFFF" };
  slide.addImage({
    path: path.join(DIR, s.file),
    x: 0,
    y: 0,
    w: 13.333,
    h: 7.5,
  });
  slide.addNotes(s.notes);
}

pres
  .writeFile({ fileName: path.join(DIR, "scion-router-operations.pptx") })
  .then((f) => console.log("wrote", f));
