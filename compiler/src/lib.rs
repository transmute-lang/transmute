use std::fs;
use std::path::Path;
use transmute_ast::parse;
use transmute_hir::resolve;
use transmute_llvm::LlvmIrGen;
use transmute_mir::make_mir;

pub fn compile_file<S: AsRef<Path>, D: AsRef<Path>>(src: &S, dst: &D) -> Result<(), String> {
    let file_content = fs::read_to_string(src)
        .map_err(|e| format!("Could not read {}: {}", src.as_ref().display(), e))?;

    compile_str(&file_content, dst)
}

pub fn compile_str<S: AsRef<str>, D: AsRef<Path>>(src: S, dst: D) -> Result<(), String> {
    let ir_gen = LlvmIrGen::default();
    parse(src.as_ref())
        .and_then(resolve)
        .and_then(make_mir)
        .and_then(|mir| ir_gen.gen(&mir))
        .and_then(|ir| ir.build_bin(transmute_crt::get_crt(), dst.as_ref()))
        .map_err(|d| d.to_string())?;

    Ok(())
}
