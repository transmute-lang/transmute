extern crate proc_macro;
use proc_macro::TokenStream;
use quote::quote;
use syn::{parse_macro_input, Data, DeriveInput};

#[proc_macro_derive(GcCallbacks)]
pub fn derive_answer_fn(item: TokenStream) -> TokenStream {
    let input = parse_macro_input!(item as DeriveInput);

    let name = input.ident;

    match input.data {
        Data::Struct(_) => {
            quote! {
                mod generated_gc_callbacks {
                    pub(super) extern "C" fn mark_recursive(ptr: *mut ()) {
                        <super::#name as crate::gc::Collectable>::mark_recursive(crate::gc::ObjectPtr::from_raw(ptr as _).unwrap());
                    }

                    pub(super) extern "C" fn free_recursive(ptr: *mut ()) {
                        <super::#name as crate::gc::Collectable>::free_recursive(crate::gc::ObjectPtr::from_raw(ptr as _).unwrap());
                    }
                }

                static CALLBACKS: GcCallbacks = GcCallbacks {
                    mark: Some(generated_gc_callbacks::mark_recursive),
                    free: Some(generated_gc_callbacks::free_recursive),
                };
            }
        }
        Data::Enum(_) | Data::Union(_) => panic!("{name} is not a struct"),
    }
    .into()
}
