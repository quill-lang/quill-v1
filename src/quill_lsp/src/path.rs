use std::{
    collections::BTreeMap,
    path::{Component, Path, PathBuf},
};

use lspower::lsp::Url;
use quill_common::location::{ModuleIdentifier, SourceFileIdentifier, SourceFileType};

/// Takes a relativised path and converts it to a source file identifier.
pub fn path_to_file(root_module: String, path: &Path) -> SourceFileIdentifier {
    let map = |component| match component {
        Component::Normal(component) => component.to_string_lossy().to_string(),
        _ => unreachable!(),
    };

    let ext = path.extension();
    let path = path.with_extension("");

    let mut components = path.components().collect::<Vec<_>>();
    let file = components.pop().unwrap();
    SourceFileIdentifier {
        module: ModuleIdentifier {
            segments: std::iter::once(root_module)
                .chain(components.into_iter().map(map))
                .map(|str| str.into())
                .collect(),
        },
        file: map(file).into(),
        file_type: if let Some(ext) = ext {
            let ext = ext.to_string_lossy().to_string();
            match ext.as_str() {
                "ql" => SourceFileType::Quill,
                "toml" => SourceFileType::Toml,
                _ => unreachable!("ext was {}", ext),
            }
        } else {
            unreachable!()
        },
    }
}

pub fn file_to_url(project_roots: &BTreeMap<String, PathBuf>, file: SourceFileIdentifier) -> Url {
    let mut iter = file
        .module
        .segments
        .into_iter()
        .chain(std::iter::once(file.file));
    let project = iter.next().unwrap().0;
    let project_root = project_roots[&project].clone();
    let segments = iter.map(|segment| segment.0);
    Url::from_file_path(
        segments
            .fold(project_root, |dir, segment| dir.join(segment))
            .with_extension(file.file_type.file_extension()),
    )
    .unwrap()
}
