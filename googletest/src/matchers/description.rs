// Copyright 2023 Google LLC
//
// Licensed under the Apache License, Version 2.0 (the "License");
// you may not use this file except in compliance with the License.
// You may obtain a copy of the License at
//
//      http://www.apache.org/licenses/LICENSE-2.0
//
// Unless required by applicable law or agreed to in writing, software
// distributed under the License is distributed on an "AS IS" BASIS,
// WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
// See the License for the specific language governing permissions and
// limitations under the License.

use std::fmt::{Display, Formatter, Result};

/// Helper structure to build better output for [`Matcher::describe`] and
/// [`Matcher::explain_match`] most notably be container matchers.
///
/// It provides simple operations to lazily format lists of strings.
///
/// Usage:
/// ```rust
/// let iter: impl Iterator<String> = ...
/// format!("{}", iter.collect::<Description>().indent().bullet_list())
/// ```
///
/// The constructor of this class is the `impl FromIterator<String>` useable
/// with `Iterator::collect()`.
#[derive(Debug)]
pub struct Description {
    elements: Vec<String>,
    indented: bool,
    list_style: ListStyle,
}

#[derive(Debug)]
enum ListStyle {
    NoList,
    Bullet,
    Enummerate,
}

impl Description {
    /// Indents the lines in [`elements`].
    ///
    /// This operation will be performed lazily when [`self`] is displayed.
    ///
    /// Note that this will indent every lines inside each element.
    /// For instance:
    ///
    /// ```rust
    /// let description = iter::once("A B C\nD E F".to_string()).collect::<Description>();
    /// verify_that!(description.indent(), displays_as(eq("  A B C\n  D E F")))
    /// ```
    pub fn indent(self) -> Self {
        Self { indented: true, ..self }
    }

    /// Bullet lists the elements of [`self`].
    ///
    /// This operation will be performed lazily when [`self`] is displayed.
    ///
    /// Note that this will only bullet list each [`elements`], not each lines
    /// in each elements.
    ///
    /// For instance:
    ///
    /// ```rust
    /// let description = iter::once("A B C\nD E F".to_string()).collect::<Description>();
    /// verify_that!(description.bullet_list(), displays_as(eq("* A B C\nD E F")))
    /// ```
    pub fn bullet_list(self) -> Self {
        Self { list_style: ListStyle::Bullet, ..self }
    }

    /// Enumerates the elements of [`self`].
    ///
    /// This operation will be performed lazily when [`self`] is displayed.
    ///
    /// Note that this will only enumerate each [`elements`], not each lines in
    /// each elements.
    ///
    /// For instance:
    ///
    /// ```rust
    /// let description = iter::once("A B C\nD E F".to_string()).collect::<Description>();
    /// verify_that!(description.indent(), displays_as(eq("  A B C\n  D E F")))
    /// ```
    pub fn enumerate(self) -> Self {
        Self { list_style: ListStyle::Enummerate, ..self }
    }

    /// Returns the length of [`elements`].
    pub fn len(&self) -> usize {
        self.elements.len()
    }

    /// Returns true if [`elements`] is empty, false otherwise.
    pub fn is_empty(&self) -> bool {
        self.elements.is_empty()
    }
}

impl Display for Description {
    fn fmt(&self, f: &mut Formatter) -> Result {
        let indent = if self.indented { 2 } else { 0 };
        let mut first = true;
        for (idx, element) in self.elements.iter().enumerate() {
            let mut first_element = true;
            for line in element.lines() {
                if first {
                    first = false;
                } else {
                    writeln!(f)?;
                }
                if first_element {
                    first_element = false;
                    match self.list_style {
                        ListStyle::NoList => {
                            write!(f, "{:indent$}{line}", "")?;
                        }
                        ListStyle::Bullet => {
                            write!(f, "{:indent$}* {line}", "")?;
                        }
                        ListStyle::Enummerate => {
                            write!(f, "{:indent$}{idx}. {line}", "")?;
                        }
                    }
                } else {
                    write!(f, "{:indent$}{line}", "")?;
                }
            }
        }
        Ok(())
    }
}

impl FromIterator<String> for Description {
    fn from_iter<T>(iter: T) -> Self
    where
        T: IntoIterator<Item = String>,
    {
        Self {
            elements: iter.into_iter().collect(),
            indented: false,
            list_style: ListStyle::NoList,
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    #[cfg(not(google3))]
    use crate as googletest;
    #[cfg(not(google3))]
    use googletest::matchers;
    use googletest::{google_test, verify_that, Result};
    use matchers::displays_as;
    use matchers::eq;

    #[google_test]
    fn description_single_element() -> Result<()> {
        let description = ["A B C".to_string()].into_iter().collect::<Description>();
        verify_that!(description, displays_as(eq("A B C")))
    }

    #[google_test]
    fn description_two_elements() -> Result<()> {
        let description =
            ["A B C".to_string(), "D E F".to_string()].into_iter().collect::<Description>();
        verify_that!(description, displays_as(eq("A B C\nD E F")))
    }

    #[google_test]
    fn description_indent_single_element() -> Result<()> {
        let description = ["A B C".to_string()].into_iter().collect::<Description>().indent();
        verify_that!(description, displays_as(eq("  A B C")))
    }

    #[google_test]
    fn description_indent_two_elements() -> Result<()> {
        let description = ["A B C".to_string(), "D E F".to_string()]
            .into_iter()
            .collect::<Description>()
            .indent();
        verify_that!(description, displays_as(eq("  A B C\n  D E F")))
    }

    #[google_test]
    fn description_indent_single_element_two_lines() -> Result<()> {
        let description =
            ["A B C\nD E F".to_string()].into_iter().collect::<Description>().indent();
        verify_that!(description, displays_as(eq("  A B C\n  D E F")))
    }

    #[google_test]
    fn description_bullet_single_element() -> Result<()> {
        let description = ["A B C".to_string()].into_iter().collect::<Description>().bullet_list();
        verify_that!(description, displays_as(eq("* A B C")))
    }

    #[google_test]
    fn description_bullet_two_elements() -> Result<()> {
        let description = ["A B C".to_string(), "D E F".to_string()]
            .into_iter()
            .collect::<Description>()
            .bullet_list();
        verify_that!(description, displays_as(eq("* A B C\n* D E F")))
    }

    #[google_test]
    fn description_bullet_single_element_two_lines() -> Result<()> {
        let description =
            ["A B C\nD E F".to_string()].into_iter().collect::<Description>().bullet_list();
        verify_that!(description, displays_as(eq("* A B C\nD E F")))
    }

    #[google_test]
    fn description_enumerate_single_element() -> Result<()> {
        let description = ["A B C".to_string()].into_iter().collect::<Description>().enumerate();
        verify_that!(description, displays_as(eq("0. A B C")))
    }

    #[google_test]
    fn description_enumerate_two_elements() -> Result<()> {
        let description = ["A B C".to_string(), "D E F".to_string()]
            .into_iter()
            .collect::<Description>()
            .enumerate();
        verify_that!(description, displays_as(eq("0. A B C\n1. D E F")))
    }

    #[google_test]
    fn description_enumerate_single_element_two_lines() -> Result<()> {
        let description =
            ["A B C\nD E F".to_string()].into_iter().collect::<Description>().enumerate();
        verify_that!(description, displays_as(eq("0. A B C\nD E F")))
    }
}
