import React, { useState } from "react";
import { Katex } from "./Katex";
import { keys, unique } from "./utils";
import { useFloating, shift, Placement } from "@floating-ui/react-dom";
import { Popover } from "@headlessui/react";
import * as Hero from "@heroicons/react/outline";
import equal from "fast-deep-equal";
import { useLocalStorage } from "./hooks";

export const App = () => {
  return (
    <div className="container flex h-screen p-10 mx-auto text-gray-50">
      <ProofSection />
    </div>
  );
};

const RULES = [
  "Boole",
  "Imp_I",
  "Imp_E",
  "Dis_E",
  "Dis_I1",
  "Dis_I2",
  "Con_I",
  "Con_E1",
  "Con_E2",
  "Uni_I",
  "Uni_E",
  "Exi_I",
  "Exi_E",
] as const;
type Rule = typeof RULES[number];
function createRule<Args = void>(opts: {
  canApply: (term: Term) => boolean;
  apply: (step: Step, args: Args) => Step[];
}) {
  return opts;
}
const applyRule = {
  Boole: createRule({
    canApply: () => true,
    apply: (step) => [
      {
        rule: null,
        assumptions: [imp(step.goal, falsify()), ...step.assumptions],
        goal: falsify(),
      },
    ],
  }),
  Imp_I: createRule({
    canApply: (term) => term.type == "imp",
    apply: (step) => {
      if (step.goal.type != "imp") throw "nooo";
      return [
        {
          rule: null,
          assumptions: [step.goal.a, ...step.assumptions],
          goal: step.goal.b,
        },
      ];
    },
  }),
  Imp_E: createRule({
    canApply: () => true,
    apply: (step) => {
      const h = hole();
      return [
        {
          rule: null,
          assumptions: step.assumptions,
          goal: imp(h, step.goal),
        },
        {
          rule: null,
          assumptions: step.assumptions,
          goal: h,
        },
      ];
    },
  }),
  Dis_E: createRule({
    canApply: () => true,
    apply: (step) => {
      const a = hole();
      const b = hole();
      return [
        {
          rule: null,
          assumptions: step.assumptions,
          goal: dis(a, b),
        },
        {
          rule: null,
          assumptions: [a, ...step.assumptions],
          goal: step.goal,
        },
        {
          rule: null,
          assumptions: [b, ...step.assumptions],
          goal: step.goal,
        },
      ];
    },
  }),
  Dis_I1: createRule({
    canApply: (term) => term.type == "dis",
    apply: (step) => {
      if (step.goal.type != "dis") throw "nooo";
      return [
        {
          rule: null,
          assumptions: step.assumptions,
          goal: step.goal.a,
        },
      ];
    },
  }),
  Dis_I2: createRule({
    canApply: (term) => term.type == "dis",
    apply: (step) => {
      if (step.goal.type != "dis") throw "nooo";
      return [
        {
          rule: null,
          assumptions: step.assumptions,
          goal: step.goal.b,
        },
      ];
    },
  }),
  Con_I: createRule({
    canApply: (term) => term.type == "con",
    apply: (step) => {
      if (step.goal.type != "con") throw "nooo";
      return [
        {
          rule: null,
          assumptions: step.assumptions,
          goal: step.goal.a,
        },
        {
          rule: null,
          assumptions: step.assumptions,
          goal: step.goal.b,
        },
      ];
    },
  }),
  Con_E1: createRule({
    canApply: () => true,
    apply: (step) => [
      {
        rule: null,
        assumptions: step.assumptions,
        goal: con(step.goal, hole()),
      },
    ],
  }),
  Con_E2: createRule({
    canApply: () => true,
    apply: (step) => [
      {
        rule: null,
        assumptions: step.assumptions,
        goal: con(hole(), step.goal),
      },
    ],
  }),
  Uni_I: createRule({
    canApply: (term) => term.type == "uni",
    apply: (step) => {
      if (step.goal.type != "uni") throw "nooo";
      let g = "c'";
      const names = allNames(step.goal.a);
      while (names.includes(g)) g += "'";
      return [
        {
          rule: null,
          assumptions: step.assumptions,
          goal: replaceQuantWith(step.goal.a, cnst(g)),
        },
      ];
    },
  }),
  Uni_E: createRule<string>({
    canApply: (term) => allNames(term).length > 0,
    apply: (step, s) => {
      return [
        {
          rule: null,
          assumptions: step.assumptions,
          goal: uni(
            preOrderMap(
              step.goal,
              (t) => {
                if (t.type == "fun" && t.name == s)
                  return hole(void 0, [quant(0), cnst(s)]);
                else return t;
              },
              {}
            )
          ),
        },
      ];
    },
  }),
  Exi_I: createRule({
    canApply: (term) => term.type == "exi",
    apply: (step) => {
      if (step.goal.type != "exi") throw "nooo";
      return [
        {
          rule: null,
          assumptions: step.assumptions,
          goal: replaceQuantWith(step.goal.a, hole()),
        },
      ];
    },
  }),
  Exi_E: createRule({
    canApply: () => true,
    apply: (step) => {
      const h = hole();
      const w = wrapper(h);
      return [
        {
          rule: null,
          assumptions: step.assumptions,
          goal: exi(h),
        },
        {
          rule: null,
          assumptions: [w, ...step.assumptions],
          goal: step.goal,
        },
      ];
    },
  }),
};
const replaceQuantWith = (term: Term, g: Term): Term =>
  preOrderMap(
    term,
    (t, depth) => {
      if (t.type == "quant" && t.depth == depth) return g;
      else if (t.type == "uni" || t.type == "exi") return [t, depth + 1];
      else return t;
    },
    1
  );

function preOrderMap<T>(
  term: Term,
  f: (t: Term, ctx: T) => Term | [Term, T],
  ctx: T
): Term {
  const res = f(term, ctx);
  if (Array.isArray(res)) {
    term = res[0];
    ctx = res[1];
  } else {
    term = res;
  }
  switch (term.type) {
    case "hole":
      return term;
    case "wrapper":
      return term;
    case "falsify":
      return term;
    case "fun":
      return fun(
        term.name,
        term.args.map((t) => preOrderMap(t, f, ctx))
      );
    case "imp":
      return imp(preOrderMap(term.a, f, ctx), preOrderMap(term.b, f, ctx));
    case "con":
      return con(preOrderMap(term.a, f, ctx), preOrderMap(term.b, f, ctx));
    case "dis":
      return dis(preOrderMap(term.a, f, ctx), preOrderMap(term.b, f, ctx));
    case "exi":
      return exi(preOrderMap(term.a, f, ctx));
    case "uni":
      return uni(preOrderMap(term.a, f, ctx));
    case "quant":
      return term;
  }
}

type HoleId = string;

type Terms = {
  hole: { id: HoleId; limit?: Term[] };
  wrapper: { over: Term };
  falsify: {};
  imp: { a: Term; b: Term };
  fun: { name: string; args: Term[] };
  con: { a: Term; b: Term };
  dis: { a: Term; b: Term };
  exi: { a: Term };
  uni: { a: Term };
  quant: { depth: number };
};
type Term = { [K in keyof Terms]: { type: K } & Terms[K] }[keyof Terms];
const termBuilder: Partial<{
  [K in Exclude<keyof Terms, "hole">]: [() => Term, string];
}> = {
  falsify: [() => falsify(), "\\bot"],
  imp: [() => imp(hole(), hole()), "\\rightarrow"],
  con: [() => con(hole(), hole()), "\\land"],
  dis: [() => dis(hole(), hole()), "\\lor"],
  exi: [() => exi(hole()), "\\exists"],
  uni: [() => uni(hole()), "\\forall"],
};

type Step = {
  rule: null | Rule;
  preview?: boolean;
  depth?: number;
  assumptions: Term[];
  goal: Term;
};

let holeSeq = 0;
const hole = (id: HoleId = (++holeSeq).toString(), limit?: Term[]): Term => ({
  type: "hole",
  limit,
  id,
});
const wrapper = (over: Term): Term => ({ type: "wrapper", over });
const falsify = (): Term => ({ type: "falsify" });
const imp = (a: Term, b: Term): Term => ({ type: "imp", a, b });
const fun = (name: string, args: Term[]): Term => ({ type: "fun", name, args });
const cnst = (name: string): Term => ({ type: "fun", name, args: [] });
const con = (a: Term, b: Term): Term => ({ type: "con", a, b });
const dis = (a: Term, b: Term): Term => ({ type: "dis", a, b });
const exi = (a: Term): Term => ({ type: "exi", a });
const uni = (a: Term): Term => ({ type: "uni", a });
const quant = (depth: number): Term => ({ type: "quant", depth });

const h0 = hole();

const ProofSection = () => {
  const [stack, setStack] = useLocalStorage<Step[][]>("naduo-steps", [
    [{ rule: null, assumptions: [], goal: h0 }],
  ]);
  const [cursor, setCursor] = useState(stack.length - 1);
  const steps = stack[cursor];
  const setSteps = (f: (steps: Step[]) => Step[]) => {
    setStack((stack) => [...stack.slice(0, cursor + 1), f(stack[cursor])]);
    setCursor(cursor + 1);
  };
  const [preview, setPreview] = useState<typeof steps | void>(void 0);

  return (
    <div
      className="relative grid w-full h-full"
      style={{ gridTemplateRows: "1fr auto" }}
    >
      <div className="overflow-y-auto">
        {(preview ?? steps).map((step, i) => (
          <StepView
            key={i}
            step={step}
            setHole={(id, term) => {
              const an = [
                ...step.assumptions.flatMap((s) => allNames(s)),
                ...allNames(step.goal),
              ];
              const opts = { id, allNames: an, term };
              setSteps((steps) =>
                steps.map((step) => ({
                  ...step,
                  assumptions: step.assumptions.map((t) => fillHole(opts, t)),
                  goal: fillHole(opts, step.goal),
                }))
              );
            }}
            onHoverRule={(r) => {
              if (r[0]) {
                const x = r as { [K in keyof A]: [K, A[K]] }[keyof A];
                setPreview(() => {
                  const ss = steps;
                  return [
                    ...ss.slice(0, i),
                    ss[i],
                    ...applyRule[x[0]].apply(ss[i], x[1] as never).map((s) => ({
                      ...s,
                      preview: true,
                      depth: (ss[i].depth ?? 0) + 1,
                    })),
                    ...ss.slice(i + 1),
                  ];
                });
              } else {
                setPreview(void 0);
              }
            }}
            chooseRule={(r) => {
              const x = r as { [K in keyof A]: [K, A[K]] }[keyof A];
              setPreview(void 0);
              setSteps((ss) => [
                ...ss.slice(0, i),
                { ...ss[i], rule: x[0] },
                ...applyRule[x[0]]
                  .apply(ss[i], x[1] as never)
                  .map((s) => ({ ...s, depth: (ss[i].depth ?? 0) + 1 })),
                ...ss.slice(i + 1),
              ]);
            }}
          />
        ))}
      </div>
      <div className="flex flex-col items-center justify-center">
        <input
          className="w-full max-w-lg"
          type="range"
          min={0}
          max={stack.length - 1}
          step={1}
          value={cursor}
          onChange={(e) => setCursor(parseInt(e.target.value))}
        />
        <div className="font-mono text-gray-500">
          {cursor + 1} / {stack.length}
        </div>
        <div className="flex text-gray-400">
          <button
            className="focus hover:text-gray-100"
            onClick={() => setCursor((c) => Math.max(c - 1, 0))}
          >
            <Hero.RewindIcon className="w-8 h-8 transition" />
          </button>
          {/* <Hero.PlayIcon className="w-8 h-8 transition" /> */}
          <button
            className="focus hover:text-gray-100"
            onClick={() => setCursor((c) => Math.min(c + 1, stack.length - 1))}
          >
            <Hero.FastForwardIcon className="w-8 h-8 transition" />
          </button>
        </div>
      </div>
    </div>
  );
};

const bumpQuant = (term: Term): Term => {
  if (term.type == "quant") return { type: "quant", depth: term.depth + 1 };
  else return term;
};
const fillHole = (
  opts: { id: HoleId; allNames: string[]; term: Term },
  src: Term
): Term => {
  // return preOrderMap(
  //   src,
  //   (t, opts) => {
  //     if (t.type == "hole" && t.id == opts.id) return opts.term;
  //     else if (t.type == "exi" || t.type == "uni")
  //       return [t, { ...opts, term: bumpQuant(opts.term) }];
  //     else return t;
  //   },
  //   opts
  // );

  switch (src.type) {
    case "hole":
      if (src.id == opts.id) return opts.term;
      else return src;
    case "wrapper":
      // TODO
      let g = "c'";
      while (opts.allNames.includes(g)) g += "'";
      const term = preOrderMap(
        opts.term,
        (t, depth) =>
          t.type == "exi" || t.type == "uni"
            ? [t, depth + 1]
            : t.type == "quant" && t.depth == depth
            ? cnst(g)
            : t,
        0
      );
      const w = fillHole({ ...opts, term }, src.over);
      if (containsHole(w)) {
        return wrapper(w);
      } else {
        return w;
      }
    case "falsify":
      return src;
    case "imp":
      return imp(fillHole(opts, src.a), fillHole(opts, src.b));
    case "fun":
      return fun(
        src.name,
        src.args.map((a) => fillHole(opts, a))
      );
    case "con":
      return con(fillHole(opts, src.a), fillHole(opts, src.b));
    case "dis":
      return dis(fillHole(opts, src.a), fillHole(opts, src.b));
    case "exi":
      return exi(fillHole({ ...opts, term: bumpQuant(opts.term) }, src.a));
    case "uni":
      return uni(fillHole({ ...opts, term: bumpQuant(opts.term) }, src.a));
    case "quant":
      return src;
  }
};
const containsHole = (src: Term): boolean => {
  switch (src.type) {
    case "hole":
      return true;
    case "wrapper":
      return containsHole(src.over);
    case "falsify":
      return false;
    case "fun":
      return !!src.args.find(containsHole);
    case "imp":
    case "con":
    case "dis":
      return containsHole(src.a) || containsHole(src.b);
    case "exi":
    case "uni":
      return containsHole(src.a);
    case "quant":
      return false;
  }
};
const depthOf = (src: Term): number => {
  switch (src.type) {
    case "hole":
      return 0;
    case "wrapper":
      return depthOf(src.over);
    case "falsify":
      return 0;
    case "imp":
    case "con":
    case "dis":
      return Math.max(depthOf(src.a), depthOf(src.b));
    case "fun":
      // TODO: Arguments
      return 0;
    case "exi":
    case "uni":
      return depthOf(src.a) + 1;
    case "quant":
      return 0;
  }
};
const allNames = (src: Term): string[] => {
  switch (src.type) {
    case "hole":
      return [];
    case "wrapper":
      return allNames(src.over);
    case "falsify":
      return [];
    case "imp":
    case "con":
    case "dis":
      return [...allNames(src.a), ...allNames(src.b)];
    case "fun":
      if (src.args.length == 0) return [src.name];
      else return src.args.flatMap(allNames);
    case "exi":
    case "uni":
      return allNames(src.a);
    case "quant":
      return [];
  }
};
type A = { [K in Rule]: Parameters<typeof applyRule[K]["apply"]>[1] };

const StepView = ({
  step,
  setHole,
  onHoverRule,
  chooseRule,
}: {
  step: Step;
  setHole: (id: HoleId, term: Term) => void;
  onHoverRule: <R extends keyof A | void>(
    rule: [R, R extends keyof A ? A[R] : void]
  ) => void;
  chooseRule: <R extends keyof A>(rule: [R, A[R]]) => void;
}) => {
  const [hovered, setHovered] = useState<{ id: HoleId; el: HTMLElement }>();
  const rect = hovered?.el.getBoundingClientRect();
  let hoveredHole = void 0 as void | Term;
  if (hovered) {
    preOrderMap(
      step.goal,
      (t) =>
        t.type == "hole" && t.id == hovered.id ? ((hoveredHole = t), t) : t,
      {}
    );
  }

  const goalDepth = depthOf(step.goal);

  return (
    <div
      className={`flex relative ${
        step.preview ? "opacity-50 pointer-events-none select-none" : ""
      }`}
    >
      <div className="text-center w-36">
        {step.assumptions.find((a) => equal(a, step.goal)) ? (
          <Katex src={`\\textbf{Assumption}`} />
        ) : step.rule ? (
          <Katex
            src={`\\textbf{${step.rule
              .replaceAll("_", " ")
              .replaceAll(/(\d)/g, "}_{$1")}}`}
          />
        ) : containsHole(step.goal) ? (
          "..."
        ) : (
          <Menu
            text="??"
            placement="bottom"
            className="w-full font-bold text-red-800"
          >
            {() => (
              <>
                {RULES.filter((r) => applyRule[r].canApply(step.goal)).map(
                  (r) =>
                    r == "Uni_E" ? (
                      <Menu
                        key={r}
                        text={
                          <Katex
                            src={`\\textbf{${r
                              .replaceAll("_", " ")
                              .replaceAll(/(\d)/g, "}_{$1")}}`}
                          />
                        }
                        placement="right-start"
                        className="p-2 border border-gray-600 hover:bg-gray-800 first:rounded-t last:rounded-b text-gray-50"
                      >
                        {() => (
                          <>
                            {unique(allNames(step.goal)).map((n) => (
                              <button
                                key={n}
                                className="p-2 border border-gray-600 hover:bg-gray-800 first:rounded-t last:rounded-b"
                                onClick={() => chooseRule([r, n])}
                                onMouseEnter={() => onHoverRule([r, n])}
                                onMouseLeave={() =>
                                  onHoverRule([void 0, void 0])
                                }
                              >
                                <Katex src={n} />
                              </button>
                            ))}
                          </>
                        )}
                      </Menu>
                    ) : (
                      <button
                        key={r}
                        className="p-2 border border-gray-600 hover:bg-gray-800 first:rounded-t last:rounded-b text-gray-50"
                        onClick={() => chooseRule([r, void 0])}
                        onMouseEnter={() => onHoverRule([r, void 0])}
                        onMouseLeave={() => onHoverRule([void 0, void 0])}
                      >
                        <Katex
                          src={`\\textbf{${r
                            .replaceAll("_", " ")
                            .replaceAll(/(\d)/g, "}_{$1")}}`}
                        />
                      </button>
                    )
                )}
              </>
            )}
          </Menu>
        )}
      </div>
      {hovered && (
        <style
          dangerouslySetInnerHTML={{
            __html: `* { --hole-${hovered.id}: #dc2626; }`,
          }}
        />
      )}
      <div onMouseLeave={() => setHovered(void 0)}>
        {hovered && rect && hoveredHole ? (
          <div
            className="fixed z-10 -translate-x-1/2"
            style={{
              top: rect.top,
              left: rect.left + rect.width / 2,
            }}
          >
            <div className="grid grid-flow-row-dense grid-cols-4 mt-5 overflow-hidden bg-gray-900 border border-gray-600 rounded shadow w-72">
              {(hoveredHole.type == "hole" && hoveredHole.limit
                ? hoveredHole.limit.map<[() => Term, string]>((t) => [
                    () => t,
                    termToTex(t, 0),
                  ])
                : (
                    [
                      [() => cnst("a"), "a"],
                      [() => cnst("b"), "b"],
                      [() => cnst("c"), "c"],
                      [() => cnst("f"), "f"],
                      [() => cnst("A"), "A"],
                      [() => cnst("B"), "B"],
                      [() => cnst("C"), "C"],
                      [() => cnst("D"), "D"],
                      [() => fun("A", [hole()]), "A(\\_)"],
                      [() => fun("B", [hole()]), "B(\\_)"],
                      [() => fun("C", [hole()]), "C(\\_)"],
                      [() => fun("f", [hole()]), "f(\\_)"],
                      [() => fun("A", [hole(), hole()]), "A(\\_, \\_)"],
                      [() => fun("B", [hole(), hole()]), "B(\\_, \\_)"],
                      [() => fun("C", [hole(), hole()]), "C(\\_, \\_)"],
                      [() => fun("f", [hole(), hole()]), "f(\\_, \\_)"],
                      ...Object.values(termBuilder),
                      ...qualiNames
                        .slice(0, goalDepth)
                        .map<[() => Term, string]>((n, i) => [
                          () => quant(-i),
                          n,
                        ]),
                      ...[
                        ...step.assumptions.flatMap(allNames),
                        ...allNames(step.goal),
                      ].map<[() => Term, string]>((n) => [() => cnst(n), n]),
                      ...step.assumptions
                        .filter(
                          (a) =>
                            step.goal.type == "imp" &&
                            a.type == "imp" &&
                            equal(step.goal.b, a.b)
                        )
                        .map<[() => Term, string]>((t) =>
                          t.type == "imp"
                            ? [() => t.a, termToTex(t.a, 0)]
                            : [() => t, ""]
                        ),
                    ] as const
                  ).filter(
                    ([_, n], i, rest) => i == rest.findIndex(([_, m]) => n == m)
                  )
              ).map(([f, tex]) => (
                <button
                  key={tex}
                  className="px-1 py-1 border border-gray-600/10 hover:bg-gray-800"
                  onClick={() => {
                    setHole(hovered.id, f());
                    setHovered(void 0);
                  }}
                >
                  <Katex src={tex} />
                </button>
              ))}
            </div>
          </div>
        ) : null}
        <div
          onMouseMove={(e) => {
            let t = e.target as HTMLElement | undefined;
            while (t && !t.id?.startsWith("hole-"))
              t = t.parentElement as HTMLElement | undefined;
            if (t) {
              if (t != hovered?.el)
                setHovered({ el: t, id: t.id.substring(5) });
            } else {
              setHovered(void 0);
            }
          }}
          style={{
            marginLeft: (step.depth ?? 0) + "em",
          }}
        >
          <Katex
            src={`\\left[${
              step.assumptions.map((t) => termToTex(t, 0)).join(", ") || "\\;"
            }\\right] \\;\\;\\; ${termToTex(step.goal, 0)}`}
          />
        </div>
      </div>
    </div>
  );
};

const termToTex = (term: Term, depth: number): string => {
  switch (term.type) {
    case "hole":
      return `\\htmlId{hole-${term.id}}{\\htmlStyle{color: var(--hole-${term.id}, #b91c1c);}{\\square}}`;
    case "wrapper":
      return `\\{ ${termToTex(term.over, depth)} \\}`;
    case "falsify":
      return "\\bot";
    case "imp":
      return `(${termToTex(term.a, depth)} \\rightarrow ${termToTex(
        term.b,
        depth
      )})`;
    case "fun":
      if (term.args.length == 0) return term.name;
      else
        return `${term.name}(${term.args
          .map((a) => termToTex(a, depth))
          .join(", ")})`;
    case "con":
      return `(${termToTex(term.a, depth)} \\land ${termToTex(term.b, depth)})`;
    case "dis":
      return `(${termToTex(term.a, depth)} \\lor ${termToTex(term.b, depth)})`;
    case "exi":
      return `\\exists ${qualiNames[depth]}. ${termToTex(term.a, depth + 1)}`;
    case "uni":
      return `\\forall ${qualiNames[depth]}. ${termToTex(term.a, depth + 1)}`;
    case "quant":
      return qualiNames[depth - term.depth];
    // return `x${term.depth}`;
  }
};

const qualiNames = ["x", "y", "z", "u", "v"];

const Menu = ({
  text,
  className,
  children,
  placement,
}: {
  text: React.ReactNode;
  className?: string;
  children: () => React.ReactElement;
  placement: Placement;
}) => {
  const { x, y, reference, floating, strategy } = useFloating({
    placement,
    middleware: [shift()],
  });

  const [show, setShow] = useState(false);

  return (
    <div
      ref={reference}
      className={className}
      onMouseEnter={() => setShow(true)}
      onMouseLeave={() => setShow(false)}
    >
      {text}
      {show && (
        <div
          ref={floating}
          style={{
            position: strategy,
            top: y ?? "",
            left: x ?? "",
          }}
          className="z-10 flex flex-col bg-gray-900 rounded shadow"
        >
          {children()}
        </div>
      )}
    </div>
  );
};
