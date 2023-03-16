#![feature(associated_type_defaults, box_patterns)]

pub mod infer;
pub mod leak;
pub mod mgu;
pub mod parsing;
pub mod spaced;
pub mod spec;
pub mod syntax;
pub mod typing;

pub type Result<V, E = String> = std::result::Result<V, E>;

#[macro_use]
extern crate lalrpop_util;

#[macro_use]
extern crate lazy_static;

fn main() {
    println!("Hello, world!")
}
