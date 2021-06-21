# SimpleIni
SimpleIni is a very simple crate to parse and write with the [INI format](https://en.wikipedia.org/wiki/INI_file)

## Licence
SimpleIni is licenced under either the [MIT licence](https://github.com/TheDutchMC/SimpleIni/blob/master/LICENCE-MIT.md), or the [Apache-2 licence](https://github.com/TheDutchMC/SimpleIni/blob/master/LICENCE-APACHE.md), at your discretion.

## Examples
**Parse an INI file**
```rs
use simpleini::Ini;

fn main() {
    let path = "/tmp/example.ini";
    let ini = match Ini::from_file(path) {
        Ok(ini) => ini,
        Err(e) => {
            eprintln!("Failed to parse /tmp/example.ini: {:?}", e);
            std::process::exit(1);
        }
    };
}
```

**Create a new INI file**
```rs
use simpleini::{Ini, IniSection};

// These are only needed when using Ini#add_section_with_values
use std::collections::HashMap;
use std::iter::FromIterator;
use std::array::IntoIter;

fn main() {
    let mut ini = Ini::new();
    ini.set("some_global", "VALUE");

    // Manually (and verbosely) create a section
    let mut section = IniSection::new("SectionA");
    section.set("some_section_variable", "OTHER_VALUE");
    ini.add_section(section);

    // Create a Section from a name and a HashMap<AsRef<str>, AsRef<str>>
    ini.add_section_with_values("SectionB", HashMap::from_iter(IntoIter::new([("var_b", "value_b")])));

    // Write the INI file to disk
    match ini.to_file("/tmp/example.ini") {
        Ok(()) => {},
        Err(e) => {
            eprintln!("Failed to write INI to disk: {:?}", e);
            std::process::exit(1);
        }
    };
}
```