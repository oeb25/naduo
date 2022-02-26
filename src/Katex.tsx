import * as React from "react";
import katex from "katex";
import "katex/dist/katex.min.css";

export const Katex: React.FC<{ src: string }> = ({ src }) => {
  const [ref, setRef] = React.useState(null as null | HTMLSpanElement);

  React.useEffect(() => {
    if (ref)
      try {
        katex.render(src, ref, { trust: true });
      } catch (e) {
        console.error("Failed to render", src, e);
        ref.innerText = src;
      }
  }, [src, ref]);

  return (
    <span
      ref={(x) => {
        setRef(x);
      }}
    ></span>
  );
};
