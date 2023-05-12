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

use crate::matcher::{MatchExplanation, Matcher, MatcherResult};
use std::{fmt::Debug, marker::PhantomData};

/// Matcher created by [`AndMatcherExt::and`].
///
/// **For internal use only. API stablility is not guaranteed!**
#[doc(hidden)]
pub struct ConjunctionMatcher<T: ?Sized, M1, M2> {
    m1: M1,
    m2: M2,
    phantom: PhantomData<T>,
}

impl<T: ?Sized, M1, M2> ConjunctionMatcher<T, M1, M2> {
    pub(crate) fn new(m1: M1, m2: M2) -> Self {
        Self { m1, m2, phantom: Default::default() }
    }
}

impl<T: Debug + ?Sized, M1: Matcher<ActualT = T>, M2: Matcher<ActualT = T>> Matcher
    for ConjunctionMatcher<T, M1, M2>
{
    type ActualT = T;

    fn matches(&self, actual: &T) -> MatcherResult {
        match (self.m1.matches(actual), self.m2.matches(actual)) {
            (MatcherResult::Matches, MatcherResult::Matches) => MatcherResult::Matches,
            _ => MatcherResult::DoesNotMatch,
        }
    }

    fn explain_match(&self, actual: &T) -> MatchExplanation {
        match (self.m1.matches(actual), self.m2.matches(actual)) {
            (MatcherResult::Matches, MatcherResult::Matches) => MatchExplanation::create(format!(
                "{} and\n{}",
                self.m1.explain_match(actual),
                self.m2.explain_match(actual)
            )),
            (MatcherResult::DoesNotMatch, MatcherResult::Matches) => self.m1.explain_match(actual),
            (MatcherResult::Matches, MatcherResult::DoesNotMatch) => self.m2.explain_match(actual),
            (MatcherResult::DoesNotMatch, MatcherResult::DoesNotMatch) => MatchExplanation::create(
                format!("{} and\n{}", self.m1.explain_match(actual), self.m2.explain_match(actual)),
            ),
        }
    }

    fn describe(&self, matcher_result: MatcherResult) -> String {
        format!("{}, and {}", self.m1.describe(matcher_result), self.m2.describe(matcher_result))
    }
}

#[cfg(test)]
mod tests {
    use crate::prelude::*;

    #[test]
    fn and_true_true_matches() -> Result<()> {
        verify_that!(1, anything().and(anything()))
    }

    #[test]
    fn and_true_false_does_not_match() -> Result<()> {
        let result = verify_that!(1, anything().and(not(anything())));
        verify_that!(
            result,
            err(displays_as(contains_substring(
                "Value of: 1\n\
                Expected: is anything, and never matches\n\
                Actual: 1, which is anything"
            )))
        )
    }

    #[test]
    fn and_false_true_does_not_match() -> Result<()> {
        let result = verify_that!(1, not(anything()).and(anything()));
        verify_that!(
            result,
            err(displays_as(contains_substring(
                "Value of: 1\n\
                Expected: never matches, and is anything\n\
                Actual: 1, which is anything"
            )))
        )
    }

    #[test]
    fn and_false_false_does_not_match() -> Result<()> {
        let result = verify_that!(1, not(anything()).and(not(anything())));
        verify_that!(
            result,
            err(displays_as(contains_substring(
                "Value of: 1\n\
                Expected: never matches, and never matches\n\
                Actual: 1, which is anything and\n\
                which is anything"
            )))
        )
    }

    #[test]
    fn chained_and_matches() -> Result<()> {
        #[derive(Debug)]
        struct Struct {
            a: i32,
            b: i32,
            c: i32,
        }
        verify_that!(
            Struct { a: 1, b: 2, c: 3 },
            field!(Struct.a, eq(1)).and(field!(Struct.b, eq(2))).and(field!(Struct.c, eq(3)))
        )
    }

    #[test]
    fn works_with_str_slices() -> Result<()> {
        verify_that!("A string", starts_with("A").and(ends_with("string")))
    }

    #[test]
    fn works_with_owned_strings() -> Result<()> {
        verify_that!("A string".to_string(), starts_with("A").and(ends_with("string")))
    }
}
