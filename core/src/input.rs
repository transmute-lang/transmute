use crate::ids::InputId;
use crate::vec_map::VecMap;
use std::fs;
use std::path::PathBuf;

pub type Inputs = VecMap<InputId, Input>;

#[derive(Debug)]
pub enum Input {
    Core,
    File(PathBuf, String),
    Internal(&'static str, &'static str),
}

impl Input {
    pub fn core() -> Self {
        Self::Core
    }

    pub fn source(&self) -> &str {
        match self {
            Input::Core => "namespace core {}",
            Input::File(_, src) => src,
            Input::Internal(_, src) => src,
        }
    }

    pub fn name(&self) -> &str {
        match self {
            Input::Core => "core",
            Input::File(path, _) => path.to_str().unwrap(),
            Input::Internal(name, _) => name,
        }
    }
}

impl TryFrom<PathBuf> for Input {
    type Error = String;

    fn try_from(value: PathBuf) -> Result<Self, Self::Error> {
        let path_buf = value
            .canonicalize()
            .map_err(|e| format!("Could not canonicalize {}: {e}", value.display()))?;

        let content = fs::read_to_string(&path_buf)
            .map_err(|e| format!("Could not read from {}: {e}", path_buf.display()))?;

        Ok(Self::File(path_buf, content))
    }
}

impl From<(&'static str, &'static str)> for Input {
    fn from((name, value): (&'static str, &'static str)) -> Self {
        Input::Internal(name, value)
    }
}
