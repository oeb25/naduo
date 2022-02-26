import React, { useCallback, useRef, useState } from "react";
import { Katex } from "./Katex";
import { useFloating, shift, Placement, offset } from "@floating-ui/react-dom";
import { atom, AtomEffect, useRecoilState, useRecoilValue } from "recoil";
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
  optionsForHole,
  Rule,
  Step,
  Term,
  termToTex,
} from "./logic";
import equal from "fast-deep-equal";
import { RadioGroup } from "@headlessui/react";

export const App = () => {
  return (
    <div
      className="relative grid h-screen"
      style={{ gridTemplateRows: "auto 1fr" }}
    >
      <div className="grid place-items-end">
        <Options />
      </div>
      <div className="container flex py-10 mx-auto">
        <ProofSection />
      </div>
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

const braceStyleState = atom<BraceStyle>({
  key: "braceStyleState",
  default: "math",
  effects: [localStorageEffect("braceStyleState")],
});

const Options = () => {
  const { x, y, reference, floating, strategy, update } = useFloating({
    placement: "left",
    middleware: [shift({ padding: 6 }), offset(4)],
  });

  const [open, setOpen] = useState(false);
  React.useEffect(() => {
    requestAnimationFrame(update);
  }, [update, open]);

  const container = useRef<HTMLDivElement>(null);

  React.useEffect(() => {
    const c = container.current;
    if (!c) return;

    const l = (e: MouseEvent | TouchEvent) => {
      if (!c.contains(e.target as Node | null)) setOpen(false);
    };

    window.addEventListener("click", l);

    return () => window.removeEventListener("click", l);
  }, []);

  const [braceStyle, setBraceStyle] = useRecoilState(braceStyleState);

  return (
    <div ref={container} className="group">
      <button ref={reference} onClick={() => setOpen((o) => !o)}>
        <Hero.CogIcon
          className={`p-2 transition opacity-50 w-9 h-9 group-hover:opacity-100 ${
            open ? "opacity-100" : ""
          }`}
        />
      </button>
      <div
        ref={floating}
        style={{
          visibility: open ? void 0 : "hidden",
          position: strategy,
          top: y ?? "",
          left: x ?? "",
        }}
        className="z-10 flex flex-col px-2 py-1 pb-2 space-y-2 rounded shadow-lg bg-stone-800 roudned"
      >
        {[1].map((i) => (
          <div key={i} className="flex flex-col">
            <RadioGroup value={braceStyle} onChange={setBraceStyle}>
              <RadioGroup.Label className="text-lg font-semibold text-center text-gray-300 border-b border-b-gray-600">
                Parenthesis style
              </RadioGroup.Label>
              <div className="flex">
                <RadioGroup.Option
                  className="flex justify-center flex-1"
                  value="math"
                >
                  {({ checked }) => (
                    <button
                      className={`transition ${checked ? "" : "opacity-50"}`}
                    >
                      <Katex src="A(f(x))" />
                    </button>
                  )}
                </RadioGroup.Option>
                <RadioGroup.Option
                  className="flex justify-center flex-1"
                  value="ml"
                >
                  {({ checked }) => (
                    <button
                      className={`transition ${checked ? "" : "opacity-50"}`}
                    >
                      <Katex src="A\:(f\:x)" />
                    </button>
                  )}
                </RadioGroup.Option>
              </div>
            </RadioGroup>
          </div>
        ))}

        <div className="absolute right-0 translate-x-full -translate-y-2 border-t-8 border-b-8 border-l-8 border-transparent shadow-lg border-l-stone-800" />
      </div>
    </div>
  );
};

const stackState = atom<Step[][]>({
  key: "stack",
  default: [[{ rule: null, assumptions: [], goal: hole() }]],
  effects: [localStorageEffect("naduo-stack")],
});

const ProofSection = () => {
  const [stack, setStack] = useRecoilState(stackState);
  const [cursor, setCursor] = useState(stack.length - 1);
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
                }))
              );
            }}
            onHoverRule={([rule, newSteps]) => {
              if (rule) {
                setPreview(() => [
                  ...steps.slice(0, i),
                  steps[i],
                  ...newSteps.map((s) => ({
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
                { ...ss[i], rule },
                ...steps.map((s) => ({ ...s, depth: (ss[i].depth ?? 0) + 1 })),
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
          <button className="focus hover:text-gray-100" onClick={back}>
            <Hero.RewindIcon className="w-8 h-8 transition" />
          </button>
          <button className="focus hover:text-gray-100" onClick={forward}>
            <Hero.FastForwardIcon className="w-8 h-8 transition" />
          </button>
        </div>
      </div>
      <div className="flex flex-col items-center justify-center">
        <button
          className="flex items-center space-x-1 text-gray-400 transition hover:text-gray-100"
          onClick={() =>
            window.navigator.clipboard.writeText(
              // encodeSteps(steps)
              stack.map(encodeSteps).reverse().join("\n")
            )
          }
        >
          <span>Export</span> <Hero.SaveIcon className="w-5 h-5" />
        </button>
      </div>
    </div>
  );
};

const StepView = ({
  step,
  setHole,
  onHoverRule,
  chooseRule,
}: {
  step: Step;
  setHole: (id: HoleId, term: Term) => void;
  onHoverRule: (rule: [Rule | void, Step[]]) => void;
  chooseRule: (rule: [Rule, Step[]]) => void;
}) => {
  const [hovered, setHovered] = useState<{ id: HoleId; el: HTMLElement }>();
  const rect = hovered?.el.getBoundingClientRect();

  const braceStyle = useRecoilValue(braceStyleState);
  const options = hovered?.id && optionsForHole(step, hovered.id, braceStyle);

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
                {applicableSteps(step).map((r) => {
                  const label = (
                    <Katex
                      src={`\\textbf{${r.rule
                        .replaceAll("_", " ")
                        .replaceAll(/(\d)/g, "}_{$1")}}`}
                    />
                  );
                  return r.options ? (
                    <Menu
                      key={r.rule}
                      text={label}
                      placement="right-start"
                      className="p-2 border border-gray-600 hover:bg-gray-800 first:rounded-t last:rounded-b text-gray-50"
                    >
                      {() => (
                        <>
                          {r.options.map(([n, apply]) => (
                            <button
                              key={n}
                              className="p-2 border border-gray-600 hover:bg-gray-800 first:rounded-t last:rounded-b"
                              onClick={() => chooseRule([r.rule, apply()])}
                              onMouseEnter={() =>
                                onHoverRule([r.rule, apply()])
                              }
                              onMouseLeave={() => onHoverRule([void 0, []])}
                            >
                              <Katex src={n} />
                            </button>
                          ))}
                        </>
                      )}
                    </Menu>
                  ) : (
                    <button
                      key={r.rule}
                      className="p-2 border border-gray-600 hover:bg-gray-800 first:rounded-t last:rounded-b text-gray-50"
                      onClick={() => chooseRule([r.rule, r.apply()])}
                      onMouseEnter={() => onHoverRule([r.rule, r.apply()])}
                      onMouseLeave={() => onHoverRule([void 0, []])}
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
            __html: `* { --hole-${hovered.id}: #dc2626; }`,
          }}
        />
      )}
      <div onMouseLeave={() => setHovered(void 0)}>
        {hovered && rect && options ? (
          <div
            className="fixed z-10 -translate-x-1/2"
            style={{
              top: rect.top,
              left: rect.left + rect.width / 2,
            }}
          >
            <div className="grid grid-flow-row-dense grid-cols-4 mt-5 overflow-hidden bg-gray-900 border border-gray-600 rounded shadow w-72">
              {options.map(([f, tex]) => (
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
            let t = e.target as HTMLElement | undefined | null;
            while (t && !t.id?.startsWith("hole-")) t = t.parentElement;
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
              step.assumptions
                .map((t) => termToTex(t, { braceStyle }))
                .join(", ") || "\\;"
            }\\right] \\;\\;\\; ${termToTex(step.goal, { braceStyle })}`}
          />
        </div>
      </div>
    </div>
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
          className="z-10 flex flex-col bg-gray-900 rounded shadow"
        >
          {children()}
        </div>
      )}
    </div>
  );
};
