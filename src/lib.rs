//! SimpleIni is a simple crate to parse and create INI files
//!
//! # Examples
//! **Read an INI file from disk**
//! ```
//! use simpleini::Ini;
//!
//! fn main() {
//!     let path = "/tmp/example.ini";
//!     let ini = match Ini::from_file(path) {
//!         Ok(ini) => ini,
//!         Err(e) => {
//!             eprintln!("Failed to parse /tmp/example.ini: {:?}", e);
//!             std::process::exit(1);
//!         }
//!     };
//! }
//! ```
//!
//! **Create a new INI file**
//! ```
//! use simpleini::{Ini, IniSection};
//!
//! // These are only needed when using Ini#add_section_with_values
//! use std::collections::HashMap;
//! use std::iter::FromIterator;
//! use std::array::IntoIter;
//!
//! fn main() {
//!     let mut ini = Ini::new();
//!     ini.set("some_global", "VALUE");
//!
//!     // Manually (and verbosely) create a section
//!     let mut section = IniSection::new("SectionA");
//!     section.set("some_section_variable", "OTHER_VALUE");
//!     ini.add_section(section);
//!
//!     // Create a Section from a name and a HashMap<AsRef<str>, AsRef<str>>
//!     ini.add_section_with_values("SectionB", HashMap::from_iter(IntoIter::new([("var_b", "value_b")])));
//!
//!     // Write the INI file to disk
//!     match ini.to_file("/tmp/example.ini") {
//!         Ok(()) => {},
//!         Err(e) => {
//!             eprintln!("Failed to write INI to disk: {:?}", e);
//!             std::process::exit(1);
//!         }
//!     };
//! }
//! ```


use std::fmt;
use std::fmt::Formatter;
use std::fmt::Write;
use std::collections::HashMap;
use std::path::Path;
use std::fs;

use regex::Regex;
use lazy_static::lazy_static;

lazy_static! {
    static ref SECTION_REGEX: Regex = Regex::new(r#"\[(.*)\]"#).unwrap();
    static ref KEY_VALUE_REGEX: Regex = Regex::new(r#"^([^=]+)=(.*)(.*)"#).unwrap();
}

/// A `Result` alias where the `Err` case is `simpleini::IniError`
pub type Result<T> = std::result::Result<T, IniError>;

/// The Error that may occur when parsing or writing with this crate
#[derive(Debug)]
pub struct IniError {
    e: String
}

impl fmt::Display for IniError {
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
        write!(f, "{}", self.e.as_str())
    }
}

impl std::error::Error for IniError {}

impl<T> From<T> for IniError where T: AsRef<str> {
    fn from(i: T) -> Self {
        let r = i.as_ref();
        Self {
            e: r.to_string()
        }
    }
}

/// Ini
#[derive(Debug, Eq, PartialEq)]
pub struct Ini {
    pub(crate) sections:   Vec<IniSection>,
    pub(crate) globals:    HashMap<String, String>
}

impl Ini {
    /// Create an empty Ini instace
    pub fn new() -> Self {
        Self {
            sections:   Vec::new(),
            globals:    HashMap::new()
        }
    }

    /// Create an Ini instance from a file
    ///
    /// # Errors
    /// Returns Err when reading the file failed
    pub fn from_file<P>(path: P) -> Result<Self> where P: AsRef<Path> {
        let path = path.as_ref();
        let contents = match fs::read_to_string(path) {
            Ok(c) => c,
            Err(e) => return Err(e.to_string().into())
        };

        Self::deserialize(contents)
    }

    /// Write the Ini instance to a file
    ///
    /// # Errors
    /// Returns Err when writing the file failed
    pub fn to_file<P>(&self, path: P) -> Result<()> where P: AsRef<Path> {
        let serialized = self.serialize()?;
        match fs::write(path, serialized) {
            Ok(_) => Ok(()),
            Err(e) => return Err(e.to_string().into())
        }
    }

    /// Deserialize an AsRef<str> into an instance of Ini
    ///
    /// # Errors
    /// Returns Err when the provided string is not valid
    pub fn deserialize<T>(input: T) -> Result<Self> where T: AsRef<str> {
        let input = input.as_ref();

        let mut globals = HashMap::new();
        let mut sections = Vec::new();
        let mut working_section = None;

        for line in input.lines() {
            let line = line.trim();

            if line.is_empty() {
                continue;
            }

            // Skip over comments
            if line.starts_with(";") {
                continue;
            }

            // A section starts with '['
            if line.starts_with("[") {
                if let Some(section) = working_section {
                    sections.push(section);
                }

                let captures = match SECTION_REGEX.captures(line) {
                    Some(c) => c,
                    None => return Err(format!("Invalid INI file. Line {} is invalid! (No matches)", line).into())
                };

                let section_name = match captures.get(1) {
                    Some(n) => n,
                    None => return Err(format!("Invalid INI File. Line {} is invalid! (Capture group 1)", line).into())
                };

                let section = IniSection::new(section_name.as_str());
                working_section = Some(section)
            } else if let Some(section) = &mut working_section {
                let (k, v) = Self::get_kv(line)?;
                section.keys.insert(k.to_string(), v.to_string());
            } else {
                let (k, v) = Self::get_kv(line)?;
                globals.insert(k.to_string(), v.to_string());
            }
        }

        if let Some(section) = working_section {
            sections.push(section);
        }

        Ok(Self {
            sections,
            globals
        })
    }

    /// Serialize an Ini instance into a String
    pub fn serialize(&self) -> Result<String> {
        let mut builder = String::new();
        for (k, v) in &self.globals {
            let _ = writeln!(&mut builder, "{}={}", k, v);
        }

        for section in &self.sections {
            let _ = writeln!(&mut builder, "");
            let _ = writeln!(&mut builder, "[{}]", section.name);
            for (k, v) in &section.keys {
                let _ = writeln!(&mut builder, "{}={}", k, v);
            }
        }

        Ok(builder)
    }

    /// Add an IniSection to the Ini instance
    pub fn add_section(&mut self, section: IniSection) {
        self.sections.push(section);
    }

    /// Add an IniSection to the Ini instance
    pub fn add_section_with_values<T, K, V>(&mut self, name: T, values: HashMap<K, V>) where T: AsRef<str>, K: AsRef<str>, V: AsRef<str> {
        let keys: HashMap<String, String> = values.iter().map(|(k, v)| (k.as_ref().to_string(), v.as_ref().to_string())).collect();
        let section = IniSection {
            name: name.as_ref().to_string(),
            keys
        };

        self.sections.push(section);
    }

    /// Get an IniSection by name from the Ini instance
    ///
    /// # Option
    /// Returns None when no IniSection exists for the provided name
    pub fn get_section<K>(&self, name: K) -> Option<&IniSection> where K: AsRef<str> {
        for section in &self.sections {
            if section.name.eq(name.as_ref()) {
                return Some(section)
            }
        }

        None
    }

    /// Get a mutable reference to an IniSection by name from the Ini instance
    ///
    /// # Option
    /// Returns None when no IniSection exists for the provided name
    pub fn get_section_mut<K>(&mut self, name: K) -> Option<&mut IniSection> where K: AsRef<str> {
        for section in &mut self.sections {
            if section.name.eq(name.as_ref()) {
                return Some(section)
            }
        }

        None
    }

    /// Get a global value from the Ini instance
    ///
    /// # Option
    /// Returns None when no global key-value pair exists for the provided key
    pub fn get<K>(&self, key: K) -> Option<&str> where K: AsRef<str> {
        match self.globals.get(key.as_ref()) {
            Some(g) => Some(g.as_str()),
            None => None
        }
    }

    /// Set a global key-value pair for the Ini instance
    pub fn set<K, V>(&mut self, key: K, value: V) where K: AsRef<str>, V: AsRef<str> {
        self.globals.insert(key.as_ref().to_string(), value.as_ref().to_string());
    }

    fn get_kv(line: &str) -> Result<(&str, &str)> {
        let captures = match KEY_VALUE_REGEX.captures(line) {
            Some(c) => c,
            None => return Err(format!("Invalid INI file. Line {} is invalid!", line).into())
        };

        let k = match captures.get(1) {
            Some(k) => k,
            None => return Err(format!("Invalid INI file. Line {} is invalid!", line).into())
        };

        let v = match captures.get(2) {
            Some(v) => v,
            None => return Err(format!("Invalid INI file. Line {} is invalid!", line).into())
        };

        Ok((k.as_str(), v.as_str()))
    }
}

/// A Section in an Ini file
#[derive(Debug, Eq, PartialEq)]
pub struct IniSection {
    /// The name of the section
    pub(crate) name: String,
    /// The key-value pairs in this section
    pub(crate) keys: HashMap<String, String>
}

impl IniSection {
    /// Create an empty IniSection instance
    pub fn new<T>(name: T) -> Self where T: AsRef<str> {
        let name = name.as_ref().to_string();
        Self {
            name,
            keys: HashMap::new()
        }
    }

    /// Set a variable inside the IniSection
    pub fn set<K, V>(&mut self, key: K, value: V) where K: AsRef<str>, V: AsRef<str> {
        self.keys.insert(key.as_ref().to_string(), value.as_ref().to_string());
    }

    /// Get a variable from the IniSection
    ///
    /// # Option
    /// Returs None when no key-value pair exists for the provided key
    pub fn get<K>(&self, key: K) -> Option<&str> where K: AsRef<str> {
        match self.keys.get(key.as_ref()) {
            Some(v) => Some(v.as_str()),
            None => None
        }
    }
}

#[cfg(test)]
mod test {
    use crate::{Ini, IniSection};
    use std::collections::HashMap;
    use std::array::IntoIter;
    use std::iter::FromIterator;

    #[test]
    fn parse_from_str() {
        let ini = "some_global=VALUE\n\n[A]\nsome_section_variable=OTHER_VALUE\n";

        let parsed = Ini::deserialize(ini).unwrap();
        let correct = Ini { globals: HashMap::from_iter(IntoIter::new([("some_global".to_string(), "VALUE".to_string())])), sections: vec![
            IniSection {
                name: "A".to_string(),
                keys: HashMap::from_iter(IntoIter::new([("some_section_variable".to_string(), "OTHER_VALUE".to_string())]))
            }
        ]};

        assert_eq!(correct, parsed);
    }

    #[test]
    fn set_replace() {
        let mut ini = Ini::new();
        ini.set("foo", "bar");
        ini.set("foo", "baz");

        let serialized = ini.serialize().unwrap();
        assert_eq!(&serialized, "foo=baz\n");
    }

    #[test]
    fn serialize_to_str() {
        let ini = "some_global=VALUE\n\n[A]\nsome_section_variable=OTHER_VALUE\n";

        let parsed = Ini::deserialize(ini).unwrap();
        let serialized = parsed.serialize().unwrap();

        assert_eq!(serialized, ini);
    }

    #[test]
    fn test_value_with_equals() {
        let mut ini = Ini::new();
        ini.set("foo", "'bar=baz'");

        let serialized = ini.serialize().unwrap();
        assert_eq!(&serialized, "foo='bar=baz'\n");

        let deserialized = Ini::deserialize(&serialized).expect("Failed to deserialize");
        assert_eq!(deserialized.get("foo").expect("Missing foo"), "'bar=baz'")
    }

    #[test]
    fn build_manually() {
        let ini = "some_global=VALUE\n\n[A]\nsome_section_variable=OTHER_VALUE\n[B]\nvar_b=value_b";
        let parsed = Ini::deserialize(ini).unwrap();

        let mut ini = Ini::new();
        ini.set("some_global", "VALUE");

        let mut section = IniSection::new("A");
        section.set("some_section_variable", "OTHER_VALUE");
        ini.add_section(section);

        ini.add_section_with_values("B", HashMap::from_iter(IntoIter::new([("var_b", "value_b")])));

        assert_eq!(parsed, ini);
    }
}