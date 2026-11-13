// Vercel serverless proxy for Twelve Data.
// The API key lives in the TWELVEDATA_KEY environment variable (set in the
// Vercel dashboard), so it never reaches the browser.
const ALLOWED = new Set(['time_series', 'quote']);
const ALLOWED_PARAMS = ['symbol', 'interval', 'outputsize'];

module.exports = async function handler(req, res) {
  const key = process.env.TWELVEDATA_KEY;
  const q = req.query || {};

  // Health check: lets the page know a shared key is available.
  if (q.ping) {
    res.setHeader('Cache-Control', 'no-store');
    return res.status(200).json({ ok: Boolean(key) });
  }

  if (!key) return res.status(503).json({ status: 'error', message: 'Server API key is not configured.' });
  if (!ALLOWED.has(q.endpoint)) return res.status(400).json({ status: 'error', message: 'Unsupported endpoint.' });

  const params = new URLSearchParams();
  for (const p of ALLOWED_PARAMS) if (q[p]) params.set(p, String(q[p]).slice(0, 32));
  if (!params.get('symbol')) return res.status(400).json({ status: 'error', message: 'Missing symbol.' });
  params.set('apikey', key);

  try {
    const r = await fetch('https://api.twelvedata.com/' + q.endpoint + '?' + params.toString());
    const body = await r.json();
    // Cache at Vercel's edge for 5 minutes so all visitors share lookups
    // and the free-plan quota lasts longer.
    if (body && body.status !== 'error') res.setHeader('Cache-Control', 's-maxage=300, stale-while-revalidate=60');
    return res.status(200).json(body);
  } catch (e) {
    return res.status(502).json({ status: 'error', message: 'Could not reach Twelve Data.' });
  }
};
