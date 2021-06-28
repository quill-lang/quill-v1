use proc_macro::TokenStream;
use quote::quote;

#[proc_macro]
pub fn generate_tests(contents: TokenStream) -> TokenStream {
    assert!(
        contents.is_empty(),
        "this macro did not expect any parameters"
    );
    quote!().into()
}
