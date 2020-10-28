## How vscode client launches a language server process

- It passes `--socket=<port>` on cmdl

https://github.com/microsoft/vscode-languageserver-node/blob/master/client/src/node/main.ts#L323

- It listens on `127.0.0.1`

https://github.com/microsoft/vscode-languageserver-node/blob/master/jsonrpc/src/node/main.ts#L197
