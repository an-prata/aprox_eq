// aprox_eq Copyright (c) 2023 Evan Overman (https://an-prata.it).
// Licensed under the MIT License.
// See LICENSE file in repository root for complete license text.

// NOTE: If ever the proc-macro stuff can be put in the same crate as other code
// that should be public this stuff should get moved to aprox_eq.

use proc_macro::TokenStream;
use proc_macro2::Span;
use quote::{format_ident, quote};
use syn::{
    self, punctuated::Punctuated, token::Comma, DeriveInput, Field, Fields, FieldsNamed,
    FieldsUnnamed, Ident, Variant,
};

#[proc_macro_derive(AproxEq)]
pub fn aprox_eq_derive(input: TokenStream) -> TokenStream {
    let ast: DeriveInput = syn::parse(input).unwrap();
    impl_aprox_eq(ast)
}

fn impl_aprox_eq(input: DeriveInput) -> TokenStream {
    let name = &input.ident;

    // Get the named struct fields, if what we got was not a struct panic.
    match &input.data {
        syn::Data::Struct(syn::DataStruct { fields, .. }) => impl_struct(name, fields),
        syn::Data::Enum(syn::DataEnum { variants, .. }) => impl_enum(name, variants),
        _ => panic!("Can only derive on struct or enums"),
    }
}

/// Creates a [`TokenStream`] with an `impl` block for `AproxEq` on the given
/// [`Ident`] with the given struct fields.
///
/// [`TokenStream`]: TokenStream
/// [`Ident`]: Ident
fn impl_struct(name: &Ident, fields: &Fields) -> TokenStream {
    match &fields {
        syn::Fields::Named(f) => {
            let field_ids = f.named.iter().map(|field| &field.ident);

            quote! {
                impl AproxEq for #name {
                    fn aprox_eq(&self, other: &Self) -> bool {
                        true #(&& self.#field_ids.aprox_eq(&other.#field_ids))*
                    }
                }
            }
        }

        syn::Fields::Unnamed(f) => {
            let field_ids = (0..f.unnamed.len()).map(syn::Index::from);

            quote! {
                impl AproxEq for #name {
                    fn aprox_eq(&self, other: &Self) -> bool {
                        true #(&& self.#field_ids.aprox_eq(&other.#field_ids))*
                    }
                }
            }
        }

        _ => panic!("Cannot derive `AproxEq` on non-struct."),
    }
    .into()
}

/// Creates a [`TokenStream`] with an `impl` block for `AproxEq` on the given
/// [`Ident`] with the given enum variants.
///
/// [`TokenStream`]: TokenStream
/// [`Ident`]: Ident
fn impl_enum(name: &Ident, variants: &Punctuated<Variant, Comma>) -> TokenStream {
    let var_impls = variants.iter().map(|variant| match &variant.fields {
        Fields::Named(FieldsNamed { named, .. }) => impl_var_named_fields(variant, named),
        Fields::Unnamed(FieldsUnnamed { unnamed, .. }) => impl_var_unnamed(variant, unnamed),
        Fields::Unit => quote! { (Self::#variant, Self::#variant) => true, },
    });

    quote! {
        impl AproxEq for #name {
            fn aprox_eq(&self, other: &Self) -> bool {
                match (self, other) {
                    #( #var_impls )*
                    _ => false,
                }
            }
        }
    }
    .into()
}

/// "implements" `AproxEq` onto the given enum variant with named fields.
/// Produces a [`proc_macro2::TokenStream`] representing a match arm that will
/// match for a tuple of two of the given enum type both being the given
/// variant. The arm will evaluate to `true` if corresponding feilds in both
/// instances are aproximately equal.
///
/// [`proc_macro2::TokenStream`]: proc_macro2::TokenStream
fn impl_var_named_fields(
    variant: &Variant,
    named: &Punctuated<Field, Comma>,
) -> proc_macro2::TokenStream {
    let idents: Vec<_> = named
        .iter()
        .map(|field| field.ident.as_ref().unwrap())
        .collect();

    let idents_self: Vec<_> = idents
        .iter()
        .map(|ident| format_ident!("self_{}", ident))
        .collect();

    let idents_other: Vec<_> = idents
        .iter()
        .map(|ident| format_ident!("other_{}", ident))
        .collect();

    let var_ident = &variant.ident;

    quote! {
        (
            Self::#var_ident { #( #idents: #idents_self ),* },
            Self::#var_ident { #( #idents: #idents_other ),* }
        ) => {
            true #( && #idents_self.aprox_eq(#idents_other) )*
        }
    }
    .into()
}

/// "implements" `AproxEq` onto the given enum variant with unnamed fields.
/// Produces a [`proc_macro2::TokenStream`] representing a match arm that will
/// match for a tuple of two of the given enum type both being the given
/// variant. The arm will evaluate to `true` if corresponding feilds in both
/// instances are aproximately equal.
///
/// [`proc_macro2::TokenStream`]: proc_macro2::TokenStream
fn impl_var_unnamed(
    variant: &Variant,
    unnamed: &Punctuated<Field, Comma>,
) -> proc_macro2::TokenStream {
    let idents_self: Vec<_> = (0..unnamed.len())
        .map(|i| Ident::new(format!("self_{}", i).as_str(), Span::call_site()))
        .collect();

    let idents_other: Vec<_> = (0..unnamed.len())
        .map(|i| Ident::new(format!("other_{}", i).as_str(), Span::call_site()))
        .collect();

    let var_ident = &variant.ident;

    quote! {
        (
            Self::#var_ident( #( #idents_self ),* ),
            Self::#var_ident( #( #idents_other ),* )
        ) => {
            true #( && #idents_self.aprox_eq(#idents_other) )*
        }
    }
    .into()
}
