import { StrictMode } from 'react';
import { createRoot } from 'react-dom/client';
import App from './App';
import { indexSiteData, loadSiteData } from './data';
import '../styles.css';

const root = createRoot(document.getElementById('root')!);
root.render(<p className="boot-message">Loading the guide.</p>);

loadSiteData().then(data => {
  root.render(<StrictMode><App index={indexSiteData(data)} /></StrictMode>);
}).catch((error: unknown) => {
  const message = error instanceof Error ? error.message : String(error);
  root.render(<div className="boot-message">
    <p>The guide data could not be loaded.</p>
    <p><code>{message}</code></p>
    <p>Serve the built site from a web server (for example <code>python3 -m http.server</code>);
      browsers do not allow pages opened from a file to fetch their data.</p>
  </div>);
});
