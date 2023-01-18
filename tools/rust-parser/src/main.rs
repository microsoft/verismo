#![feature(box_patterns)]
#![feature(proc_macro_tracked_env)]
#![feature(proc_macro_span)]
extern crate proc_macro;
use quote::quote;
use std::fs;
use syntax::*;
mod syntax;
use clap::{App, Arg};
use std::fs::OpenOptions;
use std::io::Write;

fn main() {
    let matches = App::new("My Program")
        .version("1.0")
        .author("Name <email@example.com>")
        .about("Does awesome things")
        .arg(
            Arg::with_name("infile")
                .short("i")
                .long("infile")
                .value_name("FILE")
                .help("Sets the input file to use")
                .takes_value(true),
        )
        .arg(
            Arg::with_name("indir")
                .short("d")
                .long("indir")
                .value_name("DIR")
                .help("Sets the input directory to use")
                .takes_value(true),
        )
        .arg(
            Arg::with_name("mode")
                .short("m")
                .long("mode")
                .value_name("MODE")
                .help("Sets the mode to use")
                .takes_value(true),
        )
        .arg(
            Arg::with_name("outfile")
                .short("o")
                .long("outfile")
                .value_name("OFILE")
                .help("Sets the output json file path")
                .takes_value(true),
        )
        .get_matches();

    // You can check the value of the arguments

    let mut mode = "showline";
    if let Some(m) = matches.value_of("mode") {
        mode = m;
    }
    let mut remove_proof = true;
    let mut show_line: bool = true;
    match mode {
        "example" => {
            remove_proof = true;
            show_line = false;
        }
        "showline" => {
            remove_proof = false;
            show_line = true;
        }
        _ => {}
    }
    let mut outfile = "out.json";
    if let Some(o) = matches.value_of("outfile") {
        outfile = o
    }
    if let Some(infile) = matches.value_of("infile") {
        process_file(
            &infile.to_string(),
            &outfile.to_string(),
            remove_proof,
            show_line,
        );
    }
    if let Some(indir) = matches.value_of("indir") {
        process_dir(
            &indir.to_string(),
            &outfile.to_string(),
            remove_proof,
            show_line,
        );
    }
}

fn get_cloc(file_path: &String) -> usize {
    let output = Command::new("cloc")
        .arg(file_path.as_str())
        .output()
        .expect("Failed to execute command");
    let mut cloc: String = "0".to_string();
    if output.status.success() {
        let stdout = String::from_utf8_lossy(&output.stdout);
        println!("{}", stdout);
        let l: Vec<&str> = stdout.split("\n").collect();
        let l: Vec<&str> = l[l.len() - 3].split(" ").collect();
        //println!("{}", l[l.len() - 3]);
        cloc = l[l.len() - 1].to_string();
    } else {
        let stderr = String::from_utf8_lossy(&output.stderr);
        panic!("Error: {}", stderr);
    }
    println!("\n{}", cloc);
    cloc.parse::<u32>().unwrap() as usize
}

fn process_dir(dir: &String, outfile: &String, remove_proof: bool, show_line: bool) -> Visitor {
    let entries = fs::read_dir(dir).unwrap();

    let mut top_visitor = new_visitor(remove_proof);
    for entry in entries {
        match entry {
            Ok(entry) => {
                let path = entry.path();
                println!("{:?}", path);
                if path.is_file() {
                    let filepath = fs::canonicalize(path.clone()).unwrap();
                    let filename = filepath.to_str().unwrap();
                    if filename.ends_with(".rs") {
                        let visitor =
                            process_file(&filename.to_string(), outfile, remove_proof, show_line);
                        top_visitor.merge(&visitor);
                    }
                }

                if path.is_dir() {
                    let filepath = fs::canonicalize(path.clone()).unwrap();
                    let dirname = filepath.to_str().unwrap();
                    let visitor =
                        process_dir(&dirname.to_string(), outfile, remove_proof, show_line);
                    top_visitor.merge(&visitor);
                }
            }
            Err(e) => println!("Error: {}", e),
        }
    }

    let mut file = OpenOptions::new()
        .write(true)
        .append(true)
        .create(true)
        .open(outfile)
        .unwrap();
    file.write_all((top_visitor.to_json(show_line, get_cloc(dir), dir)).as_bytes());
    top_visitor
}

use std::process::Command;

fn process_file(
    file_path: &String,
    outfile: &String,
    remove_proof: bool,
    show_line: bool,
) -> Visitor {
    let rust_code = match fs::read_to_string(file_path) {
        Ok(content) => content,
        Err(err) => {
            eprintln!("Failed to read file: {}", err);
            panic!();
        }
    };

    let parsed = syn_verus::parse_file(&rust_code).expect("Failed to parse Rust file");
    let mut visitor = new_visitor(remove_proof);

    let functions = extract_functions(
        &mut visitor,
        parsed.items,
        remove_proof,
        show_line,
        file_path,
        outfile,
    );
    let mut file = OpenOptions::new()
        .write(true)
        .append(true)
        .create(true)
        .open(outfile)
        .unwrap();

    file.write_all((visitor.to_json(show_line, get_cloc(file_path), file_path)).as_bytes());

    visitor
}

fn extract_functions(
    visitor: &mut Visitor,
    items: Vec<syn_verus::Item>,
    remove_proof: bool,
    show_line: bool,
    filepath: &String,
    outfile: &String,
) -> Vec<String> {
    let mut functions = Vec::new();
    for item in items {
        match item {
            syn_verus::Item::Fn(func) => {
                functions.push(quote! {#func}.to_string());
            }

            syn_verus::Item::Mod(m) if m.content.is_some() => {
                extract_functions(
                    visitor,
                    m.content.unwrap().1,
                    remove_proof,
                    show_line,
                    filepath,
                    outfile,
                );
            }

            syn_verus::Item::Macro(mac) if mac.mac.path.get_ident().is_some() => {
                let macro_name = mac
                    .mac
                    .path
                    .get_ident()
                    .expect(&format!("failed at {}", filepath).as_str())
                    .to_string();
                if macro_name == "verus"
                    || macro_name == "verismo_simple"
                    || macro_name == "verismo_non_secret"
                    || macro_name == "verismo"
                {
                    process_verus_code(mac.mac.tokens, visitor);
                }
            }
            _ => {}
        }
    }

    functions
}
