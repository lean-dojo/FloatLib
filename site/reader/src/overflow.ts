// Horizontal overflow cue shared by tables and Lean blocks, and the width stop of Lean blocks.
// A scroll container with hidden scrollbars (macOS, most phones) gives no sign that more text
// exists to the right, so the element carries `has-more-right` while it can still scroll that
// way and styles.css fades its right edge. `watchOverflow` keeps the class current on scroll and
// on resize; `updateOverflow` is the one-shot version for markup the reader does not own
// (chapter HTML from the build step). `fitLeanBlock` decides between the two widths a Lean
// block may have; see the comment there and .lean-block in styles.css.

export function updateOverflow(element: HTMLElement): void {
  element.classList.toggle('has-more-right',
    element.scrollLeft + element.clientWidth < element.scrollWidth - 1);
}

/**
 * Choose a Lean block's width stop. A block starts at the measure; when one of its lines does
 * not fit there, it gets `is-wide` and styles.css snaps it to the wide stop (--code-wide or what
 * the reader has). Comment lines count like code lines at the measure, so a long docstring line
 * widens the block instead of wrapping with two orphaned words; at the wide stop styles.css lets
 * comment lines wrap while code scrolls. For a wrapped statement (`is-wrap`) there is no
 * horizontal overflow to read, so we look at the line boxes instead: an inline span that wraps
 * has more than one client rect. The class is removed first so a resize can also narrow a block.
 */
export function fitLeanBlock(block: HTMLElement): void {
  const pre = block.querySelector<HTMLElement>('pre');
  if (!pre) return;
  block.classList.remove('is-wide');
  if (needsWideStop(block, pre)) block.classList.add('is-wide');
  updateOverflow(pre);
}

function needsWideStop(block: HTMLElement, pre: HTMLElement): boolean {
  if (block.classList.contains('is-wrap')) {
    for (const code of pre.querySelectorAll<HTMLElement>('.lean-line-code')) {
      if (code.getClientRects().length > 1) return true;
    }
    return false;
  }
  return pre.scrollWidth > pre.clientWidth + 1;
}

/** fitLeanBlock for every Lean block under `root`, in one pass (chapter HTML from the build). */
export function fitLeanBlocks(root: ParentNode): void {
  for (const block of root.querySelectorAll<HTMLElement>('.lean-block')) fitLeanBlock(block);
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
