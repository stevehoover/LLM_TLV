#!/usr/bin/env python3

# Self-contained tests for tlv_lint.py: one or more synthetic positive cases per rule, the exact
# BAD-SCOPE defect from the first real hierarchy run, and negative cases built from the idioms of
# the proven serv conversions and warp-v that the lint must accept.
#
# Each case writes a module directory (wip.tlv plus optional .eqy and included files) under a
# temporary directory and runs tlv_lint.py on it as fev.sh does (with --strict), then compares
# the set of reported rules with the expected set. No network, no SandPiper.
#
# Run: python3 tlv_lint_test.py   (prints "N/N cases passed", exit 1 on fail)

import os
import re
import subprocess
import sys
import tempfile

LINT = os.path.join(os.path.dirname(os.path.abspath(__file__)), "tlv_lint.py")

# A minimal serv-style module: a \TLV macro holding the logic, called from the main region.
BASE_HEAD = """\\m5_TLV_version 1d: tl-x.org
\\m5
   use(m5-1.0)

// The guts of module serv_x.
\\TLV serv_x(/_top)
   |default
      @0
         $out_x = $in_x;

\\SV
module serv_x(input i_x, output o_x);

"""
BASE_MAIN = """\\TLV
   |default
      @0
         $in_x = *i_x;
   m5+serv_x(/top)
   |default
      @0
         *o_x = $out_x;
"""
BASE_TAIL = """\\SV
endmodule
"""


def wip(main=BASE_MAIN, head=BASE_HEAD):
    return head + main + BASE_TAIL


EQY = """[gold]
read_verilog -sv -formal prepared.sv

[gate]
read_verilog -sv -formal wip.sv

[match serv_x]
{lines}

[strategy sby_seq]
use sby
"""


# Run the lint on a module directory. Returns (exit_status, [(rule, message)]).
def run_lint(mdir, strict=True):
    args = [sys.executable, LINT] + (["--strict"] if strict else []) + [mdir]
    r = subprocess.run(args, capture_output=True, text=True)
    found = []
    for line in r.stdout.splitlines():
        m = re.match(r"^(.*?):(\d+): ([A-Z0-9-]+): (.*)$", line)
        if m:
            found.append((m.group(3), m.group(4)))
        else:
            found.append(("OUTPUT", line))
    return r.returncode, found


CASES = []


# Register a case: name, {relative path: contents}, expected set of rules (empty for clean),
# optional substring that must appear in some message, and whether to run with --strict.
def case(name, files, expect, contains=None, strict=True):
    CASES.append((name, files, set(expect), contains, strict))


case("clean baseline", {"wip.tlv": wip()}, [])

case("serv idioms are clean", {"wip.tlv": wip(head="""\\m5_TLV_version 1d: tl-x.org
\\m5
   use(m5-1.0)
\\SV
   m4_include_url(['https://raw.githubusercontent.com/TL-X-org/tlv_lib/abc/fundamentals_lib.tlv'])

\\TLV serv_x(/_top)
   |default
      @0
         /*
          A block comment with $bad-looking text and |pipes inside.
          */
         /cnt_w1[0:W != 1 ? -1 \\: 0]
            <<1$cnt_lsb[3:0] = (|default<>0$reset & (RESET_STRATEGY != "NONE")) ? 4'b0000 :
                               {$cnt_lsb[2:0], ($cnt_lsb[3] & !|default<>0$cnt_done_out) \\| |default<>0$rf_ready};
         $rd_wen = $i_rd_wen & (\\|$rd_waddr);
         m5_if_eq_block(m5_cond_with_csr, 1, ['
         // WITH_CSR configuration
         $wreg0[4+WITH_CSR:0] = $trap ? {6'b100011} : {1'b0, $rd_waddr};
         '], ['
         // NO_CSR configuration
         $wreg0[4+WITH_CSR:0] = $rd_waddr;
         '])
         $neuron[10:0] = \\$signed(|default/cnt_w1[0]$cnt_lsb[3:0]) * \\$signed($o_q[4:0]) +
                             \\$signed($i_trap[4:0]);
         $cnt_r[3:0] = (W == 1) ? /cnt_w1[0]$cnt_lsb : 4'b1111;
         $Val[15:0] <= $reset ? 1 : $Val + >>1$Val;
         <<1$StorePending = $subOp;
         $out_x = $in_x ? $RETAIN : $cnt_r[0];
         \\SV_plus
            localparam CMSB = 4 - \\$clog2(W); // Counter MSB
            always_ff @(posedge clk) $$sync <= $in_x;
         m5+ifelse(m5_FORMAL, 1,
            \\TLV
               |fetch
                  @1
                     \\SV_plus
                        sram #(
                          .NB_COL(4),   // number of columns
                        ) imem (.douta(>>1$$fetch_word[7:0]));
            ,   /// Default
            \\TLV
               $fetch_word[7:0] = 8'b0;
            )

\\SV
module serv_x(input i_x, output o_x);

""", main="""\\TLV
   |default
      @0
!        $in_x = *i_x;
!        $i_trap = *i_x;
         $reset = *i_x;
   m5+serv_x(/top)
   |default
      @0
         *o_x = $out_x;
""")}, [])

case("ID-SHORT $a (strict)", {"wip.tlv": wip(main=BASE_MAIN.replace("$in_x = *i_x;", "$a = *i_x;\n         $in_x = $a;"))},
     ["ID-SHORT"], contains="$aa is legal")
case("ID-SHORT $a not reported without --strict",
     {"wip.tlv": wip(main=BASE_MAIN.replace("$in_x = *i_x;", "$a = *i_x;\n         $in_x = $a;"))}, [], strict=False)
case("ID-SHORT $i_trap is accepted", {"wip.tlv": wip(main=BASE_MAIN.replace("$in_x = *i_x;", "$i_trap = *i_x;\n         $in_x = $i_trap;"))}, [])
case("ID-SHORT /x hierarchy", {"wip.tlv": wip(main=BASE_MAIN.replace("      @0\n         $in_x = *i_x;", "      @0\n         /x\n            $in_x = *i_x;"))},
     ["ID-SHORT"], contains="/xx is legal")
case("ID-SHORT |p pipeline", {"wip.tlv": wip(main=BASE_MAIN.replace("|default\n      @0\n         $in_x", "|p\n      @0\n         $in_x"))},
     ["ID-SHORT"], contains="|pp is legal")
case("ID-CASE /Sub", {"wip.tlv": wip(main=BASE_MAIN.replace("      @0\n         $in_x = *i_x;", "      @0\n         /Sub\n            $in_x = *i_x;"))},
     ["ID-CASE"], contains="/sub")
case("ID-KEYWORD $FOO", {"wip.tlv": wip(main=BASE_MAIN.replace("$in_x = *i_x;", "$FOO = *i_x;\n         $in_x = $FOO;"))},
     ["ID-KEYWORD"], contains="$foo")
case("ID-KEYWORD leaves $ANY and $RETAIN alone",
     {"wip.tlv": wip(main=BASE_MAIN.replace("$in_x = *i_x;", "$in_x = *i_x ? $RETAIN : 1'b0;\n         $ANY = /top|default<>0$ANY;"))}, [])
case("ID-STATE-ASSIGN $Foo = ...", {"wip.tlv": wip(main=BASE_MAIN.replace("$in_x = *i_x;", "$InX = *i_x;\n         $in_x = $InX;"))},
     ["ID-STATE-ASSIGN"], contains="$InX <= ...")
case("ID-STATE-ASSIGN accepts <= and <<1", {"wip.tlv": wip(main=BASE_MAIN.replace("$in_x = *i_x;", "$InX <= *i_x;\n         <<1$InY = *i_x;\n         $in_x = $InX ^ $InY;"))}, [])

case("REGION-END column-0 code in \\TLV", {"wip.tlv": wip(main=BASE_MAIN.replace("   m5+serv_x(/top)", "$dropped = $in_x;\n   m5+serv_x(/top)"))},
     ["REGION-END"], contains="column 0 ends the \\TLV region")
case("REGION-END column-0 comment is fine", {"wip.tlv": wip(main=BASE_MAIN.replace("   m5+serv_x(/top)", "// a comment at column 0\n/* and a block\n   comment */\n   m5+serv_x(/top)"))}, [])
case("REGION-END impure line at column 0 is fine", {"wip.tlv": wip(main=BASE_MAIN.replace("         $in_x = *i_x;", "!        $in_x = *i_x;"))}, [])
case("REGION-END in \\SV_plus region only for $ lines",
     {"wip.tlv": wip(main=BASE_MAIN + "\\SV_plus\n   assign o_x = $in_x;\nwire ww = 1'b0;\n$$late = ww;\n")}, ["REGION-END"], contains="$$late")

case("INDENT-3 four-space statement", {"wip.tlv": wip(main=BASE_MAIN.replace("         $in_x = *i_x;", "          $in_x = *i_x;"))},
     ["INDENT-3"], contains="10 spaces")
case("INDENT-3 four-space scope line", {"wip.tlv": wip(main=BASE_MAIN.replace("      @0\n         $in_x", "       @0\n          $in_x"))},
     ["INDENT-3"])
case("INDENT-3 ignores continuation lines and \\SV_plus bodies",
     {"wip.tlv": wip(main=BASE_MAIN.replace("         $in_x = *i_x;", "         $in_x = *i_x ?\n                 1'b1 :\n                    1'b0;\n         \\SV_plus\n            always_comb begin\n              if (1) $$xx = 1'b0;\n            end"))}, [])
case("INDENT-TAB", {"wip.tlv": wip(main=BASE_MAIN.replace("         $in_x = *i_x;", "\t $in_x = *i_x;"))}, ["INDENT-TAB"])

RUN1_MAIN = """\\TLV
   |default
      @0
         $in_x = *i_x;
         $rgnt = /serv_rf_ram_if|default$rgnt_out;
   /serv_rf_ram_if
      |default
         @0
            $rgnt_out = /top|default<>0$in_x;
   m5+serv_x(/top)
   |default
      @0
         *o_x = $out_x & $rgnt;
"""
case("BAD-SCOPE run-1 sibling reference (/serv_rf_ram_if|default$x from /top|default)",
     {"wip.tlv": wip(main=RUN1_MAIN)}, ["BAD-SCOPE"], contains="Write /top/serv_rf_ram_if|default$rgnt_out")
case("BAD-SCOPE run-1 fixed with /top path",
     {"wip.tlv": wip(main=RUN1_MAIN.replace("/serv_rf_ram_if|default$rgnt_out", "/top/serv_rf_ram_if|default<>0$rgnt_out"))}, [])
case("BAD-SCOPE child of current scope is fine", {"wip.tlv": wip(main=BASE_MAIN.replace("         $in_x = *i_x;", "         /sub\n            $aa = *i_x;\n         $in_x = /sub$aa;"))}, [])
case("BAD-SCOPE ancestor by name is fine", {"wip.tlv": wip(main=BASE_MAIN.replace("         $in_x = *i_x;", "         $reset = *i_x;\n         /sub\n            $aa = |default<>0$reset;\n         $in_x = /sub$aa;"))}, [])
case("BAD-SCOPE sibling hierarchy under one pipeline",
     {"wip.tlv": wip(main=BASE_MAIN.replace("         $in_x = *i_x;", "         /sa\n            $aa = *i_x;\n         /sb\n            $bb = /sa$aa;\n         $in_x = /sb$bb;"))},
     ["BAD-SCOPE"], contains="Write /top|default/sa$aa")
case("BAD-SCOPE inside the called macro body, resolved at the call site",
     {"wip.tlv": wip(head=BASE_HEAD.replace("         $out_x = $in_x;", "         /sa\n            $aa = $in_x;\n         /sb\n            $bb = /sa$aa;\n         $out_x = /sb$bb;"))},
     ["BAD-SCOPE"])
case("BAD-SCOPE unknown scope is not reported (library macro may declare it)",
     {"wip.tlv": wip(main=BASE_MAIN.replace("         $in_x = *i_x;", "         m4+flop_fifo_v2(/top, |default, @0, |fifo_out, @1, 4, /trans)\n         $in_x = |fifo_out/trans<>0$data;"))}, [])
case("BAD-SCOPE in eqy match line against wip.tlv tree",
     {"wip.tlv": wip(main=BASE_MAIN.replace("         $in_x = *i_x;", "         /sub\n            $aa = *i_x;\n         $in_x = /sub$aa;")),
      "fev_full.eqy": EQY.format(lines="gold-match aa /sub<>0$aa\ngold-match in_x |default<>0$in_x")},
     ["BAD-SCOPE"], contains="Write /top|default/sub<>0$aa")
case("BAD-SCOPE through an included child macro (hierarchy combining)",
     {"child/fully_feved.tlv": BASE_HEAD.replace("serv_x", "serv_rf_ram_if").replace("$out_x = $in_x;", "$rgnt_out = $in_x;") + "\\TLV\n   m5+serv_rf_ram_if(/top)\n" + BASE_TAIL,
      "wip.tlv": wip(head=BASE_HEAD.replace("\\SV\nmodule", "\\SV\n   m4_include_lib(['../child/fully_feved.tlv'])\n\\SV\nmodule"),
                     main="""\\TLV
   |default
      @0
         $in_x = *i_x;
         $rgnt = /serv_rf_ram_if|default$rgnt_out;
   /serv_rf_ram_if
      m5+serv_rf_ram_if(/top/serv_rf_ram_if)
   m5+serv_x(/top)
   |default
      @0
         *o_x = $out_x & $rgnt & /top/serv_rf_ram_if|default<>0$rgnt_out;
""")},
     ["BAD-SCOPE"], contains="Write /top/serv_rf_ram_if|default$rgnt_out")

case("SCOPE-DUP /sa inside /sa", {"wip.tlv": wip(main=BASE_MAIN.replace("         $in_x = *i_x;", "         /sa\n            /sa\n               $aa = *i_x;\n         $in_x = /sa/sa$aa;"))},
     ["SCOPE-DUP"])
case("SCOPE-DUP macro-named scopes are not compared", {"wip.tlv": wip(main=BASE_MAIN.replace("         $in_x = *i_x;", "         /m5_row\n            /m5_row\n               $aa = *i_x;\n         $in_x = 1'b0;"))}, [])
case("SCOPE-DUP through the m5_X_HIER naming convention (/m5_YY_HIER is /yy)",
     {"wip.tlv": wip(main=BASE_MAIN.replace("         $in_x = *i_x;", "         /m5_YY_HIER\n            /m5_YY_HIER\n               $aa = *i_x;\n         $in_x = 1'b0;"))}, ["SCOPE-DUP"])
case("BAD-SCOPE resolves a child declared as /m5_YY_HIER when referenced as /yy",
     {"wip.tlv": wip(main=BASE_MAIN.replace("         $in_x = *i_x;", "         /m5_YY_HIER\n            $aa = *i_x;\n         /tb\n            /m5_YY_HIER\n               $bb = *i_x;\n            $cc = /yy[0]$bb;\n         $in_x = /yy[0]$aa ^ /tb$cc;"))}, [])
case("nothing is reported inside a macro that is never called (dead text)",
     {"wip.tlv": wip(head=BASE_HEAD + "\\TLV unused()\n   |default\n      @0\n         /sa\n            /sa\n               $aa = 1'b0;\n         /sb\n            $bb = /sa$aa;\n\n")}, [])

case("ALIGN-PLACE in eqy match line",
     {"wip.tlv": wip(main=BASE_MAIN.replace("         $in_x = *i_x;", "         /rf_ram_if\n            $rgnt = *i_x;\n         $in_x = /rf_ram_if$rgnt;")),
      "fev_full.eqy": EQY.format(lines="gold-match rgnt |default<>0/rf_ram_if$rgnt")},
     ["ALIGN-PLACE"], contains="/rf_ram_if|default<>0$rgnt")
case("ALIGN-PLACE in TLV code", {"wip.tlv": wip(main=BASE_MAIN.replace("         $in_x = *i_x;", "         /sub\n            $aa = *i_x;\n         $in_x = |default<>0/sub$aa;"))},
     ["ALIGN-PLACE"])
case("ALIGN-PLACE correct placement and Verilog shifts are fine",
     {"wip.tlv": wip(main=BASE_MAIN.replace("         $in_x = *i_x;", "         /sub\n            $aa[3:0] = {4{*i_x}};\n         $in_x = |default/sub<>0$aa[0] ^ ($aa>>2 == 0) ^ >>1$in_x;")),
      "fev_full.eqy": EQY.format(lines="gold-match aa |default/sub<>0$aa\ngold-match in_x |default>>1$in_x")}, [])

case("M5-QUOTE unbalanced [' ", {"wip.tlv": wip(main=BASE_MAIN.replace("         $in_x = *i_x;", "         $in_x = m5_if(1, ['*i_x);"))}, ["M5-QUOTE"])
case("M5-QUOTE stray ']", {"wip.tlv": wip(main=BASE_MAIN.replace("         $in_x = *i_x;", "         $in_x = *i_x; ']"))}, ["M5-QUOTE"])
case("M5-QUOTE multi-line quoted bodies and split URLs balance",
     {"wip.tlv": wip(main=BASE_MAIN.replace("         $in_x = *i_x;", "         m4_include_url(['https:/']['/x.org/lib.tlv'])\n         m5_if_eq_block(m5_cond, 1, ['\n         $in_x = *i_x;\n         '], ['\n         $in_x = 1'b0;\n         '])"))}, [])

case("M5-CONT-INDENT continuation at the call's own indentation",
     {"wip.tlv": wip(main=BASE_MAIN.replace("   m5+serv_x(/top)", "   m5+serv_x(\n   /top)"))}, ["M5-CONT-INDENT"], contains="not past the call")
case("M5-CONT-INDENT three past the call is fine",
     {"wip.tlv": wip(main=BASE_MAIN.replace("   m5+serv_x(/top)", "   m5+serv_x(\n      /top)"))}, [])
case("M5-ARG-COMMENT // inside an m5+ argument list",
     {"wip.tlv": wip(main=BASE_MAIN.replace("   m5+serv_x(/top)", "   m5+serv_x(  // the top\n      /top)"))}, ["M5-ARG-COMMENT"])
case("M5-ARG-COMMENT /// is an M5 comment and // after the call is fine",
     {"wip.tlv": wip(main=BASE_MAIN.replace("   m5+serv_x(/top)", "   m5+serv_x(  /// the top\n      /top) // done"))}, [])

case("eqy ID-KEYWORD on a gate token",
     {"wip.tlv": wip(), "fev.eqy": EQY.format(lines="gold-match in_x |default<>0$IN_X")}, ["ID-KEYWORD"])
case("multiple findings sorted and deduplicated, exit 1",
     {"wip.tlv": wip(main=BASE_MAIN.replace("         $in_x = *i_x;", "         $FOO = *i_x;\n         $in_x = $FOO & $FOO;\n          $late = 1'b0;"))},
     ["ID-KEYWORD", "INDENT-3"])


def main():
    passed = 0
    for name, files, expect, contains, strict in CASES:
        with tempfile.TemporaryDirectory() as tmp:
            mdir = os.path.join(tmp, "mod")
            os.makedirs(mdir)
            for rel, text in files.items():
                p = os.path.join(mdir, rel)
                os.makedirs(os.path.dirname(p), exist_ok=True)
                with open(p, "w") as f:
                    f.write(text)
            status, found = run_lint(mdir, strict)
            rules = {r for r, _ in found}
            ok = rules == expect and status == (1 if expect else 0)
            if ok and contains is not None:
                ok = any(contains in msg for _, msg in found)
            if ok:
                passed += 1
            else:
                print(f"FAIL: {name}")
                print(f"   expected rules {sorted(expect)}" + (f" containing {contains!r}" if contains else ""))
                print(f"   got status {status}, rules {sorted(rules)}")
                for r, msg in found:
                    print(f"      {r}: {msg[:160]}")
    print(f"{passed}/{len(CASES)} cases passed")
    return 0 if passed == len(CASES) else 1


if __name__ == "__main__":
    sys.exit(main())
