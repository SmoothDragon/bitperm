use bitperm::*;
use flowscad::*;
use anyhow::Result;


fn main() -> Result<()> {
    let x: BitCube4 = 0x1003f.into();

    let result: D3 = x.rotate_y().into()
        ;

    println!("$fn=128;\n{}", &result);
    Ok(())
}

