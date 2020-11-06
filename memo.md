## Language Server Protocol Specification

https://microsoft.github.io/language-server-protocol/specification

## VSCode Client to ELS Server Connection

Let's launch ELS on-demand from VSCode's NodeJS env, then connect over socket, implement this in form of
[`() => Promise<StreamInfo>`](https://github.com/microsoft/vscode-languageserver-node/blob/master/client/src/node/main.ts#L124)
as
[serverOptions](https://github.com/microsoft/vscode-extension-samples/blob/d559763f2b2c940852ac6172e2af012920199b0d/lsp-sample/client/src/extension.ts#L29-L36)
passed to
[new LanguageClient(...)](https://github.com/microsoft/vscode-extension-samples/blob/d559763f2b2c940852ac6172e2af012920199b0d/lsp-sample/client/src/extension.ts#L49-L54)

See:

https://github.com/microsoft/vscode-languageserver-node/blob/17b994fa6678bd14be51615fe802f7f7d3338aa2/client/src/node/main.ts#L266-L268

### configuration mechanism for ELS tcp port

`epm x edhm els/config/port` for NodeJS to read it
