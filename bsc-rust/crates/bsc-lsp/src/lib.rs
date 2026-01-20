//! LSP server for Bluespec.

use tower_lsp::jsonrpc::Result;
use tower_lsp::lsp_types::{
    CompletionParams, CompletionResponse, DidChangeTextDocumentParams,
    DidCloseTextDocumentParams, DidOpenTextDocumentParams, GotoDefinitionParams,
    GotoDefinitionResponse, Hover, HoverParams, InitializeParams, InitializeResult,
};
use tower_lsp::{Client, LanguageServer};

/// The Bluespec language server.
#[derive(Debug)]
pub struct BscLanguageServer {
    client: Client,
    // db: CompilerDatabase,  // Salsa database
}

impl BscLanguageServer {
    /// Creates a new Bluespec language server.
    #[must_use]
    pub fn new(client: Client) -> Self {
        Self { client }
    }
}

#[tower_lsp::async_trait]
impl LanguageServer for BscLanguageServer {
    async fn initialize(&self, _params: InitializeParams) -> Result<InitializeResult> {
        Ok(InitializeResult::default())
    }

    async fn shutdown(&self) -> Result<()> {
        Ok(())
    }

    async fn did_open(&self, _params: DidOpenTextDocumentParams) {
        self.client
            .log_message(tower_lsp::lsp_types::MessageType::INFO, "file opened")
            .await;
    }

    async fn did_change(&self, _params: DidChangeTextDocumentParams) {
        self.client
            .log_message(tower_lsp::lsp_types::MessageType::INFO, "file changed")
            .await;
    }

    async fn did_close(&self, _params: DidCloseTextDocumentParams) {
        self.client
            .log_message(tower_lsp::lsp_types::MessageType::INFO, "file closed")
            .await;
    }

    async fn hover(&self, _params: HoverParams) -> Result<Option<Hover>> {
        Ok(None)
    }

    async fn completion(&self, _params: CompletionParams) -> Result<Option<CompletionResponse>> {
        Ok(None)
    }

    async fn goto_definition(
        &self,
        _params: GotoDefinitionParams,
    ) -> Result<Option<GotoDefinitionResponse>> {
        Ok(None)
    }
}
