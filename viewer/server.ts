// 人間向け証明ビューワーの静的ファイルサーバー (Bun)
//
//   bun run viewer/server.ts
//   → http://localhost:8642/viewer/
//
// リポジトリルートを配信する(ビューワーが ../docs/human-proofs/*.md と
// ../Recaman/*.lean を fetch するため)。Cache-Control: no-cache を付けるので、
// レポートやビューワー本体の更新は再読込だけで反映される。

import { resolve, normalize } from "path";

const ROOT = resolve(import.meta.dir, "..");
const PORT = Number(process.env.PORT ?? 8642);

const server = Bun.serve({
  port: PORT,
  hostname: "127.0.0.1",
  async fetch(req) {
    const url = new URL(req.url);
    let pathname = decodeURIComponent(url.pathname);

    if (pathname === "/") {
      return Response.redirect("/viewer/", 302);
    }
    if (pathname.endsWith("/")) {
      pathname += "index.html";
    }

    const filePath = normalize(resolve(ROOT, "." + pathname));
    if (!filePath.startsWith(ROOT)) {
      return new Response("Forbidden", { status: 403 });
    }

    const file = Bun.file(filePath);
    if (!(await file.exists())) {
      return new Response("Not Found", { status: 404 });
    }

    const headers = {
      "Cache-Control": "no-cache",
      "Content-Type": contentType(filePath),
    };
    if (req.method === "HEAD") {
      return new Response(null, { status: 200, headers });
    }
    return new Response(file, { headers });
  },
});

function contentType(path: string): string {
  const ext = path.slice(path.lastIndexOf(".") + 1).toLowerCase();
  const types: Record<string, string> = {
    html: "text/html; charset=utf-8",
    js: "text/javascript; charset=utf-8",
    css: "text/css; charset=utf-8",
    json: "application/json; charset=utf-8",
    md: "text/markdown; charset=utf-8",
    lean: "text/plain; charset=utf-8",
    svg: "image/svg+xml",
    png: "image/png",
  };
  return types[ext] ?? "text/plain; charset=utf-8";
}

console.log(`proof-viewer: http://localhost:${server.port}/viewer/`);
