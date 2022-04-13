import React, { useCallback, useRef, useState } from "react";
import { Katex } from "./Katex";
import { useFloating, shift, Placement, offset } from "@floating-ui/react-dom";
import {
  atom,
  AtomEffect,
  selector,
  useRecoilState,
  useRecoilValue,
  useSetRecoilState,
} from "recoil";
import * as Hero from "@heroicons/react/outline";
import {
  allNames,
  applicableSteps,
  BraceStyle,
  containsHole,
  encodeSteps,
  fillHole,
  hole,
  HoleId,
  isabeleTerm,
  isabellaSteps,
  NegationStyle,
  optionsForHole,
  Rule,
  Step,
  Style,
  Term,
  termToTex,
} from "./logic";
import equal from "fast-deep-equal";
import { RadioGroup, Popover } from "@headlessui/react";
import { exercises } from "./exercises";

export const App = () => {
  const setStackState = useSetRecoilState(stackState);
  const setCursor = useSetRecoilState(cursorState);

  return (
    <div
      className="container relative grid h-screen py-10 mx-auto"
      style={{ gridTemplateRows: "auto 1fr" }}
    >
      <div className="relative flex justify-end">
        {/* <div>
          <select
            className="bg-transparent text-xs opacity-20 hover:opacity-100 transition"
            onChange={(e) => {
              setStackState([
                [{ rule: null, assumptions: [], goal: hole() }],
                [
                  {
                    rule: null,
                    assumptions: [],
                    goal: exercises[parseInt(e.target.value)],
                  },
                ],
              ]);
              setCursor(1);
            }}
          >
            {exercises.map((e, i) => (
              <option key={i} className="text-black" value={i}>
                {isabeleTerm(e)}
              </option>
            ))}
          </select>
        </div> */}
        <Options />
      </div>
      <ProofSection />
    </div>
  );
};

function localStorageEffect<T>(key: string): AtomEffect<T> {
  return ({ setSelf, onSet }) => {
    const savedValue = localStorage.getItem(key);
    if (savedValue != null) {
      setSelf(JSON.parse(savedValue));
    }

    onSet((newValue, _, isReset) => {
      isReset
        ? localStorage.removeItem(key)
        : localStorage.setItem(key, JSON.stringify(newValue));
    });
  };
}

type Theme = "light" | "dark";
const themeState = atom<Theme>({
  key: "themeState",
  default: "dark",
  effects: [
    ({ onSet, setSelf }) => {
      const update = (theme: Theme) => {
        if (theme == "dark") {
          document.documentElement.classList.add("dark");
        } else {
          document.documentElement.classList.remove("dark");
        }
      };

      if (
        localStorage.theme === "dark" ||
        (!("theme" in localStorage) &&
          window.matchMedia("(prefers-color-scheme: dark)").matches)
      ) {
        setSelf("dark");
        update("dark");
      } else {
        setSelf("light");
        update("light");
      }

      onSet(update);
    },
  ],
});
const braceStyleState = atom<BraceStyle>({
  key: "braceStyle",
  default: "math",
  effects: [localStorageEffect("braceStyleState")],
});
type AssumptionStyle = "turnstile" | "turnstile-array" | "array";
const assumptionStyleState = atom<AssumptionStyle>({
  key: "assumptionStyle",
  default: "array",
  effects: [localStorageEffect("assumptionStyleState")],
});
const negationStyleState = atom<NegationStyle>({
  key: "negationStyle",
  default: "imp",
  effects: [localStorageEffect("negationStyleState")],
});
const styleSelector = selector<Style>({
  key: "style",
  get: ({ get }) => ({
    brace: get(braceStyleState),
    negation: get(negationStyleState),
  }),
});

const PopupMenu = ({
  placement,
  icon,
  children,
}: {
  placement: Placement;
  icon: React.ReactNode;
  children: React.ReactNode | React.ReactNode[];
}) => {
  const { x, y, reference, floating, strategy, update } = useFloating({
    placement,
    middleware: [shift({ padding: 6 }), offset(4)],
  });

  return (
    <Popover className="group">
      {({ open }) => (
        <>
          <Popover.Button
            ref={reference}
            className={`transition opacity-50 group-hover:opacity-100 ${
              open ? "opacity-100" : ""
            }`}
          >
            {icon}
          </Popover.Button>
          <Popover.Panel
            ref={floating}
            style={{
              visibility: open ? void 0 : "hidden",
              position: strategy,
              top: y ?? "",
              left: x ?? "",
            }}
            className="z-10 flex flex-col w-64 px-2 py-1 pb-2 space-y-2 bg-gray-100 rounded shadow-lg dark:bg-stone-800 roudned"
          >
            {children}

            <div
              className={`absolute right-0 translate-x-full -translate-y-2 ${
                placement == "left-end" ? "bottom-0" : ""
              } border-t-8 border-b-8 border-l-8 border-transparent shadow-lg border-l-gray-100 dark:border-l-stone-800`}
            />
          </Popover.Panel>
        </>
      )}
    </Popover>
  );
};

const Options = () => {
  const [theme, setTheme] = useRecoilState(themeState);
  const [braceStyle, setBraceStyle] = useRecoilState(braceStyleState);
  const [assumptionStyle, setAssumptionStyle] =
    useRecoilState(assumptionStyleState);
  const [negationStyle, setNegationStyle] = useRecoilState(negationStyleState);

  return (
    <PopupMenu
      icon={<Hero.CogIcon className="p-2 w-9 h-9" />}
      placement="left-start"
    >
      <RadioGroup
        value={theme}
        onChange={setTheme}
        className="flex flex-col space-y-1"
      >
        <RadioGroup.Label className="text-lg font-semibold text-center text-gray-600 border-b dark:text-gray-300 border-gray-600/10 dark:border-gray-600/50 transition">
          Color theme
        </RadioGroup.Label>
        <div className="flex">
          <RadioGroup.Option
            className="flex justify-center flex-1 p-2 cursor-pointer"
            value="light"
          >
            {({ checked }) => (
              <button className={`transition ${checked ? "" : "opacity-25"}`}>
                <Hero.SunIcon className="w-6 h-6" />
              </button>
            )}
          </RadioGroup.Option>
          <RadioGroup.Option
            className="flex justify-center flex-1 p-2 cursor-pointer"
            value="dark"
          >
            {({ checked }) => (
              <button className={`transition ${checked ? "" : "opacity-25"}`}>
                <Hero.MoonIcon className="w-6 h-6" />
              </button>
            )}
          </RadioGroup.Option>
        </div>
      </RadioGroup>
      <RadioGroup
        value={braceStyle}
        onChange={setBraceStyle}
        className="flex flex-col space-y-1"
      >
        <RadioGroup.Label className="text-lg font-semibold text-center text-gray-600 border-b dark:text-gray-300 border-gray-600/10 dark:border-gray-600/50">
          Parenthesis style
        </RadioGroup.Label>
        <div className="flex">
          <RadioGroup.Option
            className="flex justify-center flex-1 p-2 cursor-pointer"
            value="math"
          >
            {({ checked }) => (
              <button className={`transition ${checked ? "" : "opacity-25"}`}>
                <Katex src="A(f(x))" />
              </button>
            )}
          </RadioGroup.Option>
          <RadioGroup.Option
            className="flex justify-center flex-1 p-2 cursor-pointer"
            value="ml"
          >
            {({ checked }) => (
              <button className={`transition ${checked ? "" : "opacity-25"}`}>
                <Katex src="A\:(f\:x)" />
              </button>
            )}
          </RadioGroup.Option>
        </div>
      </RadioGroup>
      <RadioGroup
        value={negationStyle}
        onChange={setNegationStyle}
        className="flex flex-col space-y-1"
      >
        <RadioGroup.Label className="text-lg font-semibold text-center text-gray-600 border-b dark:text-gray-300 border-gray-600/10 dark:border-gray-600/50">
          Negation style
        </RadioGroup.Label>
        <div className="flex">
          <RadioGroup.Option
            className="flex justify-center flex-1 p-2 cursor-pointer"
            value="imp"
          >
            {({ checked }) => (
              <button className={`transition ${checked ? "" : "opacity-25"}`}>
                <Katex src="A \rightarrow \bot" />
              </button>
            )}
          </RadioGroup.Option>
          <RadioGroup.Option
            className="flex justify-center flex-1 p-2 cursor-pointer"
            value="neg"
          >
            {({ checked }) => (
              <button className={`transition ${checked ? "" : "opacity-25"}`}>
                <Katex src="\neg A" />
              </button>
            )}
          </RadioGroup.Option>
        </div>
      </RadioGroup>
      <RadioGroup
        value={assumptionStyle}
        onChange={setAssumptionStyle}
        className="flex flex-col space-y-1"
      >
        <RadioGroup.Label className="text-lg font-semibold text-center text-gray-600 border-b dark:text-gray-300 border-gray-600/10 dark:border-gray-600/50">
          Assumption style
        </RadioGroup.Label>
        <div className="flex">
          <RadioGroup.Option
            className="flex justify-center flex-1 p-2 cursor-pointer"
            value="turnstile"
          >
            {({ checked }) => (
              <button className={`transition ${checked ? "" : "opacity-25"}`}>
                <Katex src="\Gamma \vdash \Delta" />
              </button>
            )}
          </RadioGroup.Option>
          <RadioGroup.Option
            className="flex justify-center flex-1 p-2 cursor-pointer"
            value="turnstile-array"
          >
            {({ checked }) => (
              <button className={`transition ${checked ? "" : "opacity-25"}`}>
                <Katex src="[\Gamma] \vdash \Delta" />
              </button>
            )}
          </RadioGroup.Option>
          <RadioGroup.Option
            className="flex justify-center flex-1 p-2 cursor-pointer"
            value="array"
          >
            {({ checked }) => (
              <button className={`transition ${checked ? "" : "opacity-25"}`}>
                <Katex src="[\Gamma] \;\; \Delta" />
              </button>
            )}
          </RadioGroup.Option>
        </div>
      </RadioGroup>
    </PopupMenu>
  );
};

const cursorState = atom<number>({
  key: "cursor",
  default: 0,
  effects: [localStorageEffect("naduo-cursor")],
});
const stackState = atom<Step[][]>({
  key: "stack",
  default: [[{ rule: null, assumptions: [], goal: hole() }]],
  effects: [localStorageEffect("naduo-stack")],
});

const ProofSection = () => {
  const [stack, setStack] = useRecoilState(stackState);
  const [cursorI, setCursor] = useRecoilState(cursorState);
  const cursor = Math.min(cursorI, stack.length - 1);
  const back = useCallback(
    () => setCursor((c) => Math.max(c - 1, 0)),
    [setCursor]
  );
  const forward = useCallback(
    () => setCursor((c) => Math.min(c + 1, stack.length - 1)),
    [setCursor, stack.length]
  );
  const controls = useRef({ back, forward });
  controls.current = { back, forward };
  const steps = stack[cursor];
  const setSteps = (f: (steps: Step[]) => Step[]) => {
    setStack((stack) => [...stack.slice(0, cursor + 1), f(stack[cursor])]);
    setCursor(cursor + 1);
  };
  const [preview, setPreview] = useState<typeof steps | void>(void 0);

  React.useEffect(() => {
    const listener = (e: KeyboardEvent) => {
      if (e.metaKey || e.ctrlKey) {
        if (e.key == "z")
          if (e.shiftKey) controls.current.forward();
          else controls.current.back();
      }
      if (e.key == "ArrowLeft") controls.current.back();
      if (e.key == "ArrowRight") controls.current.forward();
    };

    window.addEventListener("keydown", listener);
    return () => window.removeEventListener("keydown", listener);
  }, [back, forward]);

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
                  intros: step.intros ? fillHole(opts, step.intros) : void 0,
                }))
              );
            }}
            onHoverRule={(x) => {
              if (x) {
                const [rule, newSteps] = x;
                setPreview(() => [
                  ...steps.slice(0, i),
                  { ...steps[i], intros: newSteps.intros || void 0 },
                  ...newSteps.steps.map((s) => ({
                    ...s,
                    preview: true,
                    depth: (steps[i].depth ?? 0) + 1,
                  })),
                  ...steps.slice(i + 1),
                ]);
              } else {
                setPreview(void 0);
              }
            }}
            chooseRule={([rule, steps]) => {
              setPreview(void 0);
              setSteps((ss) => [
                ...ss.slice(0, i),
                { ...ss[i], rule, intros: steps.intros || void 0 },
                ...steps.steps.map((s) => ({
                  ...s,
                  depth: (ss[i].depth ?? 0) + 1,
                })),
                ...ss.slice(i + 1),
              ]);
            }}
          />
        ))}
      </div>
      {/* <details>
        <pre className="text-xs">
          {isabellaSteps(steps)
            .split("\n")
            .map((l, i) => {
              if (l == correct[i])
                return (
                  <span>
                    {l}
                    <br />
                  </span>
                );

              return (
                <span className="text-red-600">
                  {l}
                  <br />
                  <span className="text-gray-400">{correct[i]}</span>
                  <br />
                </span>
              );
            })}
        </pre>
      </details> */}
      <div className="grid" style={{ gridTemplateColumns: "1fr 1fr 1fr" }}>
        <div />
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
              className="focus hover:text-gray-600 hover:dark:text-gray-100"
              onClick={back}
            >
              <Hero.RewindIcon className="w-8 h-8 transition" />
            </button>
            <button
              className="focus hover:text-gray-600 hover:dark:text-gray-100"
              onClick={forward}
            >
              <Hero.FastForwardIcon className="w-8 h-8 transition" />
            </button>
          </div>
        </div>
        <div className="flex items-end justify-end p-2">
          <PopupMenu
            icon={<Hero.DownloadIcon className="p-2 w-9 h-9" />}
            placement="left-end"
          >
            <div className="text-lg font-semibold text-center text-gray-600 border-b dark:text-gray-300 border-gray-600/10 dark:border-gray-600/50">
              Export
            </div>

            <button
              className="flex items-center space-x-1 text-gray-400 transition hover:text-gray-600 hover:dark:text-gray-100"
              onClick={() =>
                window.navigator.clipboard.writeText(
                  encodeSteps(steps)
                  // stack.map(encodeSteps).reverse().join("\n")
                )
              }
            >
              <span className="flex-1">Copy as NaDeA</span>
              <Hero.ClipboardCopyIcon className="w-5 h-5" />
            </button>
            <button
              className="flex items-center space-x-1 text-gray-400 transition hover:text-gray-600 hover:dark:text-gray-100"
              onClick={() =>
                window.navigator.clipboard.writeText(isabellaSteps(steps))
              }
            >
              <span className="flex-1">Copy as Isabelle</span>{" "}
              <Hero.ClipboardCopyIcon className="w-5 h-5" />
            </button>
            {/* <button
              className="flex items-center space-x-1 text-gray-400 transition hover:text-gray-600 hover:dark:text-gray-100"
              onClick={() =>
                window.navigator.clipboard.writeText(JSON.stringify(stack))
              }
            >
              <span className="flex-1">Copy as JSON</span>{" "}
              <Hero.ClipboardCopyIcon className="w-5 h-5" />
            </button> */}
          </PopupMenu>
        </div>
      </div>
    </div>
  );
};

const hoveredState = atom<HoleId | null>({
  key: "hovered-hole",
  default: null,
});

const StepView = ({
  step,
  setHole,
  onHoverRule,
  chooseRule,
}: {
  step: Step;
  setHole: (id: HoleId, term: Term) => void;
  onHoverRule: (
    rule: void | [Rule, { steps: Step[]; intros: Term | void }]
  ) => void;
  chooseRule: (rule: [Rule, { steps: Step[]; intros: Term | void }]) => void;
}) => {
  const hovered = useRecoilValue(hoveredState);

  const style = useRecoilValue(styleSelector);
  const assumptionStyle = useRecoilValue(assumptionStyleState);

  const StepRenderHole = React.useMemo(() => RenderHole(setHole, step), [step]);

  return (
    <div
      className={`flex relative ${
        step.preview ? "opacity-50 pointer-events-none select-none" : ""
      }`}
    >
      <div className="text-center w-36">
        {step.assumptions.find((a) => equal(a, step.goal)) ? (
          <Katex src={`\\textbf{Assumption}`} RenderHole={StepRenderHole} />
        ) : step.rule ? (
          <Katex
            src={`\\textbf{${step.rule
              .replaceAll("_", " ")
              .replaceAll(/(\d)/g, "}_{$1")}}`}
            RenderHole={StepRenderHole}
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
                {applicableSteps(step).map((r) => {
                  const label = (
                    <Katex
                      src={`\\textbf{${r.rule
                        .replaceAll("_", " ")
                        .replaceAll(/(\d)/g, "}_{$1")}}`}
                      RenderHole={StepRenderHole}
                    />
                  );
                  return r.options ? (
                    <Menu
                      key={r.rule}
                      text={label}
                      placement="right-start"
                      className="p-2 text-gray-800 border border-gray-600/10 dark:border-gray-600 hover:dark:bg-stone-800 hover:bg-white first:rounded-t last:rounded-b dark:text-gray-50"
                    >
                      {() => (
                        <>
                          {r.options.map(([n, apply]) => (
                            <button
                              key={n}
                              className="p-2 border border-gray-600/10 hover:bg-white dark:border-gray-600 hover:dark:bg-stone-800 first:rounded-t last:rounded-b"
                              onClick={() => chooseRule([r.rule, apply()])}
                              onMouseEnter={() =>
                                onHoverRule([r.rule, apply()])
                              }
                              onMouseLeave={() => onHoverRule(void 0)}
                            >
                              <Katex src={n} RenderHole={StepRenderHole} />
                            </button>
                          ))}
                        </>
                      )}
                    </Menu>
                  ) : (
                    <button
                      key={r.rule}
                      className="p-2 text-gray-800 border border-gray-600/10 dark:border-gray-600 hover:dark:bg-stone-800 hover:bg-white first:rounded-t last:rounded-b dark:text-gray-50"
                      onClick={() => chooseRule([r.rule, r.apply()])}
                      onMouseEnter={() => onHoverRule([r.rule, r.apply()])}
                      onMouseLeave={() => onHoverRule(void 0)}
                    >
                      {label}
                    </button>
                  );
                })}
              </>
            )}
          </Menu>
        )}
      </div>
      {hovered && (
        <style
          dangerouslySetInnerHTML={{
            __html: `* { --hole-${hovered}: #dc2626; --hole-${hovered}-scale: 1.2; --hole-${hovered}-z: 5; }`,
          }}
        />
      )}
      <div>
        <div
          style={{
            marginLeft: (step.depth ?? 0) + "em",
          }}
        >
          <Katex
            src={
              {
                array: `\\left[${
                  step.assumptions
                    .map((t) => termToTex(t, { style }))
                    .join(", ") || "\\;"
                }\\right] \\;\\;\\; ${termToTex(step.goal, { style })}`,
                turnstile: `${
                  step.assumptions
                    .map((t) => termToTex(t, { style }))
                    .join("\\;\\;\\;\\;") || "\\;"
                } \\vdash ${termToTex(step.goal, { style })}`,
                "turnstile-array": `\\left[${
                  step.assumptions
                    .map((t) => termToTex(t, { style }))
                    .join(", ") || "\\;"
                }\\right] \\vdash ${termToTex(step.goal, { style })}`,
              }[assumptionStyle]
            }
            RenderHole={StepRenderHole}
          />
        </div>
      </div>
    </div>
  );
};

const RenderHole =
  (setHole: (id: HoleId, term: Term) => void, step: Step) =>
  ({ hid }: { hid: HoleId }) => {
    const style = useRecoilValue(styleSelector);
    const [hovered, setHovered] = useRecoilState(hoveredState);
    const [hoveredThis, setHoveredThis] = useState(false);
    const options = hovered && optionsForHole(step, hovered, style);

    return (
      <span
        className="relative"
        onMouseEnter={() => {
          setHovered(hid);
          setHoveredThis(true);
        }}
        onMouseLeave={() => {
          setHovered(null);
          setHoveredThis(false);
        }}
      >
        <span
          style={{
            color: `var(--hole-${hid}, #b91c1c)`,
            transform: `scale(var(--hole-${hid}-scale, 1))`,
            position: "relative",
            zIndex: `var(--hole-${hid}-z, 0)`,
            display: "inline-flex",
            transition: "all 200ms ease",
          }}
        >
          □
        </span>
        {hoveredThis && options ? (
          <div className="z-10 -translate-x-1/2 absolute left-1/2 translate-y-[calc(100%-1em)] bottom-0 flex flex-col items-center pt-3">
            <div
              className="grid grid-flow-row-dense grid-cols-4 overflow-hidden bg-gray-100 rounded shadow dark:border dark:border-gray-600 dark:bg-stone-900 w-80"
              style={{
                gridTemplateColumns: `repeat(${Math.min(
                  options.length,
                  4
                )}, 1fr)`,
              }}
            >
              {options.map(([f, tex]) => (
                <button
                  key={tex}
                  className={`px-1 py-1 border hover:bg-white !border-gray-600/10 hover:dark:bg-stone-800 ${
                    tex.length > 20 ? "col-start-1 col-span-full" : ""
                  }`}
                  onClick={() => {
                    setHole(hovered, f());
                    setHovered(null);
                  }}
                >
                  <Katex src={tex} />
                </button>
              ))}
            </div>
          </div>
        ) : null}
      </span>
    );
  };

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
          className="z-10 flex flex-col rounded shadow dark:bg-stone-900 bg-gray-50"
        >
          {children()}
        </div>
      )}
    </div>
  );
};

const correct = `
theorem "semantics e f g (Imp (Uni (Pre ''A'' [Var 0, Fun ''f'' [Var 0]])) (Uni (Exi (Pre ''A'' [Var 1, Var 0]))))"
proof (rule soundness)
  show "OK (Imp (Uni (Pre ''A'' [Var 0, Fun ''f'' [Var 0]])) (Uni (Exi (Pre ''A'' [Var 1, Var 0])))) []"
  proof (rule Imp_I)
    show "OK (Uni (Exi (Pre ''A'' [Var 1, Var 0]))) [Uni (Pre ''A'' [Var 0, Fun ''f'' [Var 0]])]"
    proof (rule Uni_I)
      have "OK (Exi (Pre ''A'' [Fun ''c*'' [], Var 0])) [Uni (Pre ''A'' [Var 0, Fun ''f'' [Var 0]])]"
      proof (rule Exi_I)
        have "OK (Uni (Pre ''A'' [Var 0, Fun ''f'' [Var 0]])) [Uni (Pre ''A'' [Var 0, Fun ''f'' [Var 0]])]"
          by (rule Assume) simp
        then have "OK (sub 0 (Fun ''c*'' []) (Pre ''A'' [Var 0, Fun ''f'' [Var 0]])) [Uni (Pre ''A'' [Var 0, Fun ''f'' [Var 0]])]"
          by (rule Uni_E)
        then have "OK (Pre ''A'' [Fun ''c*'' [], Fun ''f'' [Fun ''c*'' []]]) [Uni (Pre ''A'' [Var 0, Fun ''f'' [Var 0]])]"
          by simp
        then show "OK (sub 0 (Fun ''f'' [Fun ''c*'' []]) (Pre ''A'' [Fun ''c*'' [], Var 0])) [Uni (Pre ''A'' [Var 0, Fun ''f'' [Var 0]])]"
          by simp
      qed
      then show "OK (sub 0 (Fun ''c*'' []) (Exi (Pre ''A'' [Var 1, Var 0]))) [Uni (Pre ''A'' [Var 0, Fun ''f'' [Var 0]])]"
        by simp
    qed simp
  qed
qed`
  .trim()
  .split("\n");
