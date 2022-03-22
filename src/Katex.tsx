import * as React from "react";
import katex from "katex";
import "katex/dist/katex.min.css";
import ReactDOM from "react-dom";
import { HoleId } from "./logic";

export const Katex: React.FC<{
  src: string;
  RenderHole?: (props: { hid: HoleId }) => React.ReactElement;
}> = ({ src, RenderHole }) => {
  const [ref, setRef] = React.useState(null as null | HTMLSpanElement);
  const [_, setUpdate] = React.useState(false);

  React.useEffect(() => {
    if (ref)
      try {
        katex.render(src, ref, { trust: true, strict: "ignore" });
        if (RenderHole) {
          setUpdate((u) => !u);
          for (const hole of ref.querySelectorAll("*[data-hole] > .mord.amsrm"))
            hole.childNodes[0].remove();
        }
      } catch (e) {
        console.error("Failed to render", src, e);
        ref.innerText = src;
      }
  }, [src, ref]);

  const holes: HTMLSpanElement[] = ref
    ? Array.from(ref.querySelectorAll("*[data-hole] > .mord.amsrm"))
    : [];

  return (
    <>
      <span ref={(x) => setRef(x)}></span>
      {RenderHole &&
        holes.map((hole) =>
          ReactDOM.createPortal(
            <RenderHole hid={hole.parentElement!.dataset["hole"]!} />,
            hole
          )
        )}
    </>
  );
};
