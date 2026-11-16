"""Minimal stdio MCP client for lean-lsp-mcp (trial, 2026-11-16).

Run with the MCP SDK that ships with lean-lsp-mcp:
    uvx --from lean-lsp-mcp python experiments/autoresearch_trial_20261116/lean_lsp_mcp/client.py list
    uvx --from lean-lsp-mcp python .../client.py call TOOL '{"json": "args"}' [TOOL2 '{...}' ...]

The server is started as `uvx lean-lsp-mcp` with LEAN_PROJECT_PATH = repo root.
Every call is timed; output is printed as JSON lines.
"""
from __future__ import annotations

import asyncio
import json
import os
import sys
import time
from pathlib import Path

from mcp import ClientSession, StdioServerParameters
from mcp.client.stdio import stdio_client

ROOT = Path(__file__).resolve().parents[3]


def text_of(result) -> str:
    parts = []
    for c in result.content:
        parts.append(getattr(c, "text", str(c)))
    return "\n".join(parts)


async def main(argv: list[str]) -> None:
    env = dict(os.environ, LEAN_PROJECT_PATH=str(ROOT))
    params = StdioServerParameters(command="uvx", args=["lean-lsp-mcp"], env=env, cwd=str(ROOT))
    async with stdio_client(params) as (r, w):
        async with ClientSession(r, w) as s:
            t0 = time.time()
            await s.initialize()
            print(json.dumps({"event": "initialized", "seconds": round(time.time() - t0, 2)}), flush=True)
            if argv[0] == "list":
                tools = await s.list_tools()
                for t in tools.tools:
                    props = list((getattr(t, "input_schema", None) or getattr(t, "inputSchema", None) or {}).get("properties", {}).keys())
                    req = (getattr(t, "input_schema", None) or getattr(t, "inputSchema", None) or {}).get("required", [])
                    print(json.dumps({"tool": t.name, "args": props, "required": req,
                                      "desc": (t.description or "").split("\n")[0][:160]}, ensure_ascii=False))
                return
            assert argv[0] == "call"
            pairs = argv[1:]
            for i in range(0, len(pairs), 2):
                name, args = pairs[i], json.loads(pairs[i + 1])
                t1 = time.time()
                try:
                    res = await s.call_tool(name, args)
                    out = text_of(res)
                    err = bool(getattr(res, "isError", False))
                except Exception as exc:  # report and continue
                    out, err = repr(exc), True
                print(json.dumps({"tool": name, "args": args, "seconds": round(time.time() - t1, 2),
                                  "error": err, "output": out}, ensure_ascii=False), flush=True)


if __name__ == "__main__":
    asyncio.run(main(sys.argv[1:]))
