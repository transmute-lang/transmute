extern crate proc_macro;
use proc_macro::TokenStream;
use quote::quote;
use syn::{parse_macro_input, Data, DeriveInput};

#[proc_macro_derive(GcCallbacks)]
pub fn derive_gc_callbacks(item: TokenStream) -> TokenStream {
    let input = parse_macro_input!(item as DeriveInput);

    let name = input.ident;

    match input.data {
        Data::Struct(_) => {
            quote! {
                #[automatically_derived]
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

#[proc_macro_derive(MapKeyVTable)]
pub fn derive_gc_mapkey_vtable(item: TokenStream) -> TokenStream {
    let input = parse_macro_input!(item as DeriveInput);

    let name = input.ident;

    match input.data {
        Data::Struct(_) => {
            quote! {
                #[automatically_derived]
                mod generated_mapkey_vtable {
                    pub extern "C" fn hash(str: *const (), hasher: *mut ()) {
                        use std::hash::Hash;
                        let hasher = hasher as *mut std::hash::DefaultHasher;
                        let str = crate::gc::ObjectPtr::from_raw(str as *mut super::Str).unwrap();
                        std::hash::Hash::hash(str.as_ref(), unsafe { &mut *hasher });
                    }

                    pub extern "C" fn equals(a: *const (), b: *const ()) -> bool {
                        let a = crate::gc::ObjectPtr::from_raw(a as *mut super::#name).unwrap();
                        let b = crate::gc::ObjectPtr::from_raw(b as *mut super::#name).unwrap();
                        a.as_ref().eq(b.as_ref())
                    }

                    #[no_mangle]
                    static STDLIB_STR_MAPKEY_VTABLE: crate::stdlib::map::MapKeyVTable = crate::stdlib::map::MapKeyVTable {
                        hash: hash,
                        equals: equals,
                    };
                }
            }
        }
        Data::Enum(_) | Data::Union(_) => panic!("{name} is not a struct"),
    }
        .into()
}
