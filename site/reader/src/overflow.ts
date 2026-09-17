// Horizontal overflow cue shared by tables and Lean blocks.
// A scroll container with hidden scrollbars (macOS, most phones) gives no sign that more text
// exists to the right, so the element carries `has-more-right` while it can still scroll that
// way and styles.css fades its right edge. `watchOverflow` keeps the class current on scroll and
// on resize; `updateOverflow` is the one-shot version for markup the reader does not own
// (chapter HTML from the build step).

export function updateOverflow(element: HTMLElement): void {
  element.classList.toggle('has-more-right',
    element.scrollLeft + element.clientWidth < element.scrollWidth - 1);
}

export function watchOverflow(element: HTMLElement): () => void {
  const update = () => updateOverflow(element);
  element.addEventListener('scroll', update, { passive: true });
  const observer = new ResizeObserver(update);
  observer.observe(element);
  update();
  return () => {
    element.removeEventListener('scroll', update);
    observer.disconnect();
  };
}
