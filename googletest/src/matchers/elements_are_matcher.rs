// Copyright 2022 Google LLC
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

// There are no visible documentation elements in this module; the declarative
// macro is documented at the top level.
#![doc(hidden)]

/// Matches a container's elements to each matcher in order.
///
/// This macro produces a matcher against a container. It takes as arguments a
/// sequence of matchers each of which should respectively match the
/// corresponding element of the actual value.
///
/// ```
/// # use googletest::prelude::*;
/// verify_that!(vec![1, 2, 3], elements_are![eq(1), anything(), gt(0).and(lt(123))])
/// #    .unwrap();
/// ```
///
/// The actual value must be a container implementing [`IntoIterator`]. This
/// includes standard containers, slices (when dereferenced) and arrays.
///
/// ```
/// # use googletest::prelude::*;
/// let vector = vec![1, 2, 3];
/// let slice = vector.as_slice();
/// verify_that!(*slice, elements_are![eq(1), anything(), gt(0).and(lt(123))])
/// #    .unwrap();
/// ```
///
/// This can also be omitted in [`verify_that!`] macros and replaced with square
/// brackets.
///
/// ```
/// # use googletest::prelude::*;
///  verify_that!(vec![1, 2], [eq(1), eq(2)])
/// #     .unwrap();
/// ```
///
/// Note: This behavior is only possible in [`verify_that!`] macros. In any
/// other cases, it is still necessary to use the
/// [`elements_are!`][crate::elements_are] macro.
///
/// ```compile_fail
/// # use googletest::prelude::*;
/// verify_that!(vec![vec![1,2], vec![3]], [[eq(1), eq(2)], [eq(3)]])
/// # .unwrap();
/// ```
///
/// Use this instead:
/// ```
/// # use googletest::prelude::*;
/// verify_that!(vec![vec![1,2], vec![3]], [elements_are![eq(1), eq(2)], elements_are![eq(3)]])
/// # .unwrap();
/// ```
///
/// This matcher does not support matching directly against an [`Iterator`]. To
/// match against an iterator, use [`Iterator::collect`] to build a [`Vec`].
///
/// Do not use this with unordered containers, since that will lead to flaky
/// tests. Use [`unordered_elements_are!`][crate::unordered_elements_are]
/// instead.
///
/// [`IntoIterator`]: std::iter::IntoIterator
/// [`Iterator`]: std::iter::Iterator
/// [`Iterator::collect`]: std::iter::Iterator::collect
/// [`Vec`]: std::vec::Vec
#[macro_export]
macro_rules! elements_are {
    ($($matcher:expr),* $(,)?) => {{
        use $crate::matchers::elements_are_matcher::internal::ElementsAre;
        ElementsAre::new(vec![$(Box::new($matcher)),*])
    }}
}

/// Module for use only by the procedural macros in this module.
///
/// **For internal use only. API stablility is not guaranteed!**
#[doc(hidden)]
pub mod internal {
    use crate::matcher::{Matcher, MatcherResult};
    use crate::matcher_support::description::Description;
    use crate::matcher_support::zipped_iterator::zip;
    use std::{fmt::Debug, marker::PhantomData};

    /// This struct is meant to be used only by the macro `elements_are!`.
    ///
    /// **For internal use only. API stablility is not guaranteed!**
    #[doc(hidden)]
    pub struct ElementsAre<'a, ContainerT: ?Sized, T: Debug> {
        elements: Vec<Box<dyn Matcher<ActualT = T> + 'a>>,
        phantom: PhantomData<ContainerT>,
    }

    impl<'a, ContainerT: ?Sized, T: Debug> ElementsAre<'a, ContainerT, T> {
        /// Factory only intended for use in the macro `elements_are!`.
        ///
        /// **For internal use only. API stablility is not guaranteed!**
        #[doc(hidden)]
        pub fn new(elements: Vec<Box<dyn Matcher<ActualT = T> + 'a>>) -> Self {
            Self { elements, phantom: Default::default() }
        }
    }

    impl<'a, T: Debug, ContainerT: Debug + ?Sized> Matcher for ElementsAre<'a, ContainerT, T>
    where
        for<'b> &'b ContainerT: IntoIterator<Item = &'b T>,
    {
        type ActualT = ContainerT;

        fn matches(&self, actual: &ContainerT) -> MatcherResult {
            let mut zipped_iterator = zip(actual.into_iter(), self.elements.iter());
            for (a, e) in zipped_iterator.by_ref() {
                if e.matches(a).is_no_match() {
                    return MatcherResult::NoMatch;
                }
            }
            if !zipped_iterator.has_size_mismatch() {
                MatcherResult::Match
            } else {
                MatcherResult::NoMatch
            }
        }

        fn explain_match(&self, actual: &ContainerT) -> String {
            let actual_iterator = actual.into_iter();
            let mut zipped_iterator = zip(actual_iterator, self.elements.iter());
            let mut mismatches = Vec::new();
            for (idx, (a, e)) in zipped_iterator.by_ref().enumerate() {
                if e.matches(a).is_no_match() {
                    mismatches.push(format!("element #{idx} is {a:?}, {}", e.explain_match(a)));
                }
            }
            if mismatches.is_empty() {
                if !zipped_iterator.has_size_mismatch() {
                    "whose elements all match".to_string()
                } else {
                    format!("whose size is {}", zipped_iterator.left_size())
                }
            } else if mismatches.len() == 1 {
                let mismatches = mismatches.into_iter().collect::<Description>();
                format!("where {mismatches}")
            } else {
                let mismatches = mismatches.into_iter().collect::<Description>();
                format!("where:\n{}", mismatches.bullet_list().indent())
            }
        }

        fn describe(&self, matcher_result: MatcherResult) -> String {
            format!(
                "{} elements:\n{}",
                if matcher_result.into() { "has" } else { "doesn't have" },
                &self
                    .elements
                    .iter()
                    .map(|matcher| matcher.describe(MatcherResult::Match))
                    .collect::<Description>()
                    .enumerate()
                    .indent()
            )
        }
    }
}
