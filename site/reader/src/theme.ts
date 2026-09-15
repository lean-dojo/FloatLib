import { useEffect, useState } from 'react';

// Dark mode follows prefers-color-scheme until the reader picks a theme; the choice is stored in
// localStorage and applied before first paint by an inline script in index.html.
export type Theme = 'light' | 'dark';
const STORAGE_KEY = 'floatlib-theme';

function systemTheme(): Theme {
  return window.matchMedia('(prefers-color-scheme: dark)').matches ? 'dark' : 'light';
}

function storedTheme(): Theme | null {
  try {
    const value = localStorage.getItem(STORAGE_KEY);
    return value === 'light' || value === 'dark' ? value : null;
  } catch { return null; }
}

export function effectiveTheme(): Theme {
  const pinned = document.documentElement.getAttribute('data-theme');
  if (pinned === 'light' || pinned === 'dark') return pinned;
  return storedTheme() ?? systemTheme();
}

function apply(theme: Theme | null): void {
  if (theme) document.documentElement.setAttribute('data-theme', theme);
  else document.documentElement.removeAttribute('data-theme');
}

export function useTheme(): [Theme, () => void, boolean] {
  const [theme, setTheme] = useState<Theme>(effectiveTheme);
  const [explicit, setExplicit] = useState<boolean>(() => storedTheme() !== null);
  useEffect(() => {
    const media = window.matchMedia('(prefers-color-scheme: dark)');
    const follow = () => { if (storedTheme() === null) setTheme(systemTheme()); };
    media.addEventListener('change', follow);
    return () => media.removeEventListener('change', follow);
  }, []);
  const toggle = () => {
    const next: Theme = theme === 'dark' ? 'light' : 'dark';
    // Choosing the system's own scheme again means "follow the system" rather than a pinned choice.
    if (next === systemTheme()) {
      try { localStorage.removeItem(STORAGE_KEY); } catch { /* ignore */ }
      apply(null);
      setExplicit(false);
    } else {
      try { localStorage.setItem(STORAGE_KEY, next); } catch { /* ignore */ }
      apply(next);
      setExplicit(true);
    }
    setTheme(next);
  };
  return [theme, toggle, explicit];
}
