#![allow(dead_code)]

use std::arch::x86_64;
use std::cmp::max;
use std::collections::{HashMap, HashSet};
use std::hash::Hash;
use std::thread::yield_now;
use itertools::Itertools;

#[derive(Debug, PartialEq, Eq, PartialOrd, Ord, Clone, Hash)]
enum Term{
    Lambda(Box<Term>),
    App(Box<Term>, Box<Term>),
    Index(u8)
}

use Term::*;

fn term_size(term: &Term) -> u32 {
    match term {
        Term::Lambda(x) => 2 + term_size(x),
        Term::App(x, y) => 2 + term_size(x) + term_size(y),
        Term::Index(n) => (n + 1).into(),
    }
}

fn term_openness(term: &Term) -> u8 {
    match term {
        Term::Lambda(x) => {
            let x_openness = term_openness(x);
            if x_openness == 0 {
                0
            } else {
                x_openness - 1
            }
        }
        Term::App(x, y) => term_openness(x).max(term_openness(y)),
        /*  */Term::Index(n) => *n,
    }
}

fn is_closed(term: &Term) -> bool {
    term_openness(term) == 0
}

/*
    n -> 111{n times}0
    λ -> 00
    A -> 01
    these last two I don't remember which is which but it doesn't matter 
    and is easy to fix later
 */
fn term_to_bit_list_recur(out: &mut Vec<bool>, term: &Term) {
    match term {
        Index(n) => {
            for _ in 0..*n {
                out.push(true);
            }
            out.push(false);
        },
        Lambda(inner_term) => {
            out.push(false);
            out.push(false);
            term_to_bit_list_recur(out, inner_term);
        },
        App(left_term, right_term) => {
            out.push(false);
            out.push(true);
            term_to_bit_list_recur(out, left_term);
            term_to_bit_list_recur(out, right_term);
        },
    }
}

fn term_to_bit_list(term: &Term) -> Vec<bool> {
    let mut out = vec![];
    term_to_bit_list_recur(&mut out, term);
    out
}

fn bit_array_to_byte(bits: &[bool; 8]) -> u8 {
    let mut out = 0u8;
    for bit in bits[0..=6].iter() {
        if *bit {
            out += 1;
        }
        out *= 2;
    }
    if bits[7] {out += 1}
    out
}

fn bit_list_to_byte_list(bools: Vec<bool>) -> Vec<u8> {
    assert_eq!(bools.len() % 8, 0);
    let num_bytes = bools.len() / 8;
    let mut out = vec![];
    for byte_idx in 0..num_bytes {
        let thing = &bools[byte_idx*8.. (byte_idx+1)*8].try_into().unwrap();
        out.push(bit_array_to_byte(thing));
    }
    out
}

fn vec_u8_to_u64(bytes: Vec<u8>) -> u64 {
    assert_eq!(bytes.len(), 8);
    let byte_slice = bytes.try_into().unwrap();
    u64::from_be_bytes(byte_slice)    
}

/*
 takes a term
 if the term is sizze 63 or less, converts to a u64, otherwise returns none
 the conversion is, the first block of zeros is padding, then there is a 1 
 indicating the end of padding, then thhere is the bits for the term itself
 so a term which was 63 bits would be 1{term}, while id, which is the four bits
 0010 is 0..{59 zeros}..010010
 */
fn term_to_u64(term: &Term) -> Option<u64> {
    let term_bits = term_to_bit_list(term);
    if term_bits.len() > 63 {
        return None
    }
    let padding_zero_count = 63 - term_bits.len();
    let mut all_bits = vec![];
    for _ in 0..padding_zero_count {
        all_bits.push(false);
    }
    // the end of the padding
    all_bits.push(true);
    all_bits.extend(term_bits);
    assert_eq!(all_bits.len(), 64);
    Some(vec_u8_to_u64(bit_list_to_byte_list(all_bits)))
}

fn re_de_bruijn_substituent_recur(body_level: u8, substituent: &Term, substituent_level: u8) -> Term {
    assert!(body_level > 0);
    if body_level == 1 { 
        return substituent.clone() 
    };
    match substituent {
        Index(n) => 
            if *n > substituent_level {Index(n + body_level - 1)} else {Index(*n)},
        Lambda(x) => 
            Lambda(Box::new(
                re_de_bruijn_substituent_recur(body_level, x, substituent_level+1)
            )),
        App(x, y) => 
            App(Box::new(re_de_bruijn_substituent_recur(body_level, x, substituent_level)),
                Box::new(re_de_bruijn_substituent_recur(body_level, y, substituent_level))
            ),
    }
}

fn re_de_bruijn_substituent(level: u8, substituent: &Term) -> Term {
    re_de_bruijn_substituent_recur(level, substituent, 0)
}

fn substitute_level(body: Term, substituent: &Term, level: u8) -> Term {
    match body {
        Index(n) => {
            if n == level {
                re_de_bruijn_substituent(level, substituent)
            } else if n > level {
                // in something like λ6, we need to take into account that there is 
                // one fewer lambda between the variable and its target now
                assert!(n != 1, "body {} substi {} level {}", print_term(&body), print_term(&substituent), level);
                Index(n-1)
            } else {
                // whereas in something like λλλ1, we don't need to change the 1
                Index(n) 
            }
        },
        Lambda(x) => Lambda(Box::new(substitute_level(*x, substituent, level+1))),
        App(x, y) => 
            App(Box::new(substitute_level(*x, substituent, level)), 
                Box::new(substitute_level(*y, substituent, level)))
    }
}


// if you have a term like (λT) S then body is T and substituent is S 
fn substitute(body: Term, substituent: &Term) -> Term {
    // dbg!(format!("substituting {} into {}", print_term(substituent), print_term(&body)));
    let ans = substitute_level(body, &substituent, 1);
    // dbg!(format!("ans: {}", print_term(&ans)));
    ans
}

// weak head normal form, E := (\x -> term) or (x term_1 . . . term_n)
// returns none if there is no reduction
fn whnf_reduce_step(term: Term) -> Option<Term> {
    match term {
        Lambda(_) => None,
        Index(_) => None,
        App(x, y) => {
            // we might need to reduce two things. first, reduce x to whnf. second, 
            // if that x is a lambda, then we need to substitute. 
            if let Some(x_reduced) = whnf_reduce_step(*x.clone()) {
                Some(App(Box::new(x_reduced), y))
            } else {
                match *x {
                    App(_, _) => None,
                    Index(_) => None,
                    Lambda(z) => Some(substitute(*z, &y)),
                }
            }
        },
    }
}

fn whnf_reduce(mut term: Term, reduce_limit: u32) -> (Term, u32) {
    let mut counter = 0; 
    while let Some(reduced_term) = whnf_reduce_step(term.clone()) {
        term = reduced_term;
        counter += 1;
        if counter == reduce_limit {
            break
        }
    }
    (term, counter)
}

// normal form, ie E = (\x. E) or x E_1 . . . E_n
// returns None if there is no reduction
fn nf_reduce_step(term: Term) -> Option<Term> {
    match term {
        Index(_) => None,
        Lambda(x) => 
        if let Some(new_term) = nf_reduce_step(*x) {
            Some(Lambda(Box::new(new_term)))
        } else {
            None
        },
        App(x, y) => 
            // first reduce x to whnf, if it becomes a lambda, then substitute. 
            // otherwise, reduce first x, then y to nf. 
            if let Some(x_reduced) = whnf_reduce_step(*x.clone()) {
                Some(App(Box::new(x_reduced), y))
            } else if let Lambda(z) = *x.clone() {
                Some(substitute(*z, &y))
            } else if let Some(x_reduced) = nf_reduce_step(*x.clone()) {
                Some(App(Box::new(x_reduced), y))
            } else if let Some(y_reduced) = nf_reduce_step(*y.clone()) {
                Some(App(x, Box::new(y_reduced)))
            } else {
                None
            },
    }
}


// (Term, u32, bool)
// (the term after reduction, the number of steps the term was reduced, whether the size limit was reached)
fn nf_reduce(term: &Term, reduce_limit: u32, size_limit: u32) -> (Term, u32, bool) {
    // let orig_term = term.clone();
    let mut counter = 0;
    // let mut printed = 0;
    let mut cur_term = term.clone();
    while let Some(reduced_term) = nf_reduce_step(cur_term.clone()) {
        let cur_size = term_size(&cur_term);
        // if cur_size > 64 { //&& printed < 5 {
        //     if printed == 0 {
        //         println!("size {} reducing large term {}", term_size(&orig_term), print_term(&orig_term));
        //         }
        //         printed += 1;
        //         // println!("cur size {} cur term {}", cur_size, print_term(&cur_term));
        //         println!("cur size {}", cur_size);
        //         }
        
        if cur_size > size_limit {
            return (cur_term, counter, true)
        }
        cur_term = reduced_term;
        counter += 1;
        if counter == reduce_limit {
            break
        }
    }
    (cur_term, counter, false)
}


/* 
    dp relation: count(0, *) = 0, count (1, *) = 0
    count(s, o) = 
          1 if s == o+1 else 0 
        + count(x-2, y+1) if o > 0 else (count(s-2, 0) + count(s-2, 1))
        + sum (z from 0 to x-2) {
            let left  = sum (p from 0 to o-1) count(z, p)
            let right = sum (p from 0 to o-1) count(x-2-z, p)
            count(z, o) * right + left * count(x-2-z, o) + count(z, o) * count(x-2-z, 0)
          }
*/
fn dp_counting_terms_of_size_open(target_size: usize, target_openness: usize) -> u64 {
    //size is the first index, openness is the second
    let mut table = vec![];
    for size in 0..=target_size {
        table.push(vec![]);
        let max_openness = target_openness + (target_size - size) / 2;
        for _ in 0..=max_openness {
            table[size].push(u64::MAX);
        }
    }
    for size in 0..=1.min(target_size) {
        let max_openness = target_openness + (target_size - size) / 2;
        for openness in 0..=max_openness {
            table[size][openness] = 0;
        }
    }
    for size in 2..=target_size {
        let max_openness = target_openness + (target_size - size) / 2;
        for openness in 0..=max_openness {
            let index_term_count = if size == openness + 1 {1} else {0};
            let lambda_term_count = if openness == 0 {
                table[size-2][0] + table[size-2][1]
            } else {
                table[size-2][openness+1]
            };
            let mut app_term_count = 0;
            for z in 0..=(size-2) {
                let mut left = 0;
                let mut right = 0;
                for sub_openness in 0..openness {
                    left += table[z][sub_openness];
                    right += table[size-2-z][sub_openness];
                }
                app_term_count += left * table[size-2-z][openness];
                app_term_count += table[z][openness] * right;
                app_term_count += table[z][openness] * table[size-2-z][openness];
            }
            // dbg!(size, openness, index_term_count, lambda_term_count, app_term_count);
            table[size][openness] = index_term_count + lambda_term_count + app_term_count;
        }
    }
    // dbg!(&table);
    table[target_size][target_openness]
}

/* 
    dp relation: count(0, *) = 0, count (1, *) = 0
    count(s, o) = 
          1 if s == o+1 else 0 
        + count(x-2, y+1) if o > 0 else (count(s-2, 0) + count(s-2, 1))
        + sum (z from 0 to x-2) {
            let left  = sum (p from 0 to o-1) count(z, p)
            let right = sum (p from 0 to o-1) count(x-2-z, p)
            count(z, o) * right + left * count(x-2-z, o) + count(z, o) * count(x-2-z, 0)
          }

The DP relation from the previous function applies almost verbatim here. Just, 
instead of adding to the count, we add terms to the vec. Then we return the table 
directly. 

Return type: Vec<Vec<Vec<Term>>>
The three indices are size, openness, and then a Vec<Term> listing all terms of that (s, o) pair. 
*/
fn dp_list_terms_of_size_open(target_size: usize, target_openness: usize) -> Vec<Vec<Vec<Term>>> {
    let mut table: Vec<Vec<Vec<Term>>> = vec![];
    for size in 0..=target_size {
        table.push(vec![]);
        let max_openness = target_openness + (target_size - size) / 2;
        for _ in 0..=max_openness {
            table[size].push(vec![]);
        }
    }
    // we don't need the size 0, 1 basecase, because the vectors start empty,
    // which is the basecase in question

    for size in 2..=target_size {
        let max_openness = target_openness + (target_size - size) / 2;
        for openness in 0..=max_openness {
            // println!("\n");
            // dbg!(size, openness);
            let mut new_term_list = vec![];
            // index term case
            if size == openness + 1 
                {new_term_list.push(Index(openness.try_into().unwrap()))}
            // println!("open {}", print_terms(&new_term_list));
            // lambda term case
            if openness == 0 {
                for smaller_term in &table[size-2][0] {
                    new_term_list.push(Lambda(Box::new(smaller_term.clone())));
                    // println!("lambda 0 {}", print_terms(&new_term_list));
                }
                for smaller_term in &table[size-2][1] {
                    new_term_list.push(Lambda(Box::new(smaller_term.clone())));
                    // println!("lambda 1 {}", print_terms(&new_term_list));
                }
            } else {
                for smaller_term in &table[size-2][openness+1] {
                    new_term_list.push(Lambda(Box::new(smaller_term.clone())));
                    // println!("lambda 2 {}", print_terms(&new_term_list));
                }
            }

            // app term case
            for z in 0..=(size-2) {
                let mut left = vec![];
                let mut right = vec![];
                for sub_openness in 0..openness {
                    for left_term in &table[z][sub_openness] {
                        left.push(left_term)
                    }
                    for right_term in &table[size-2-z][sub_openness] {
                        right.push(right_term)
                    }
                }
                // println!("\n z {}", z);
                // println!("left {}", print_term_refs(&left));
                // println!("right {}", print_term_refs(&right));
                // println!("t[s-2-z][o] {}", print_terms(&table[size-2-z][openness]));
                // println!("t[z][o] {}", print_terms(&table[z][openness]));
                // left * table[size-2-z][openness];
                for (x, y) in left.into_iter().cartesian_product(&table[size-2-z][openness]) {
                    new_term_list.push(App(
                        Box::new(x.clone()), Box::new(y.clone())));
                    // println!("app 0 {}", print_terms(&new_term_list));
                }
                // table[z][openness] * right;
                for (x, y) in (&table[z][openness]).into_iter().cartesian_product(&right) {
                    new_term_list.push(App(
                        Box::new(x.clone()), Box::new((*y).clone())));
                    // println!("app 1 {}", print_terms(&new_term_list));
                }
                // table[z][openness] * table[size-2-z][openness];
                for (x, y) in (&table[z][openness]).into_iter().cartesian_product(&table[size-2-z][openness]) {
                    new_term_list.push(App(
                        Box::new(x.clone()), Box::new(y.clone())));
                    // println!("app 2 {}", print_terms(&new_term_list));
                }
            }
         // dbg!(size, openness, index_term_count, lambda_term_count, app_term_count);
         if let Some(dup) = find_duplicate(&new_term_list) {
            panic!("found duplicate at size {} open {} which is {}", size, openness, print_term(dup));
         }
         table[size][openness] = new_term_list;
        }
    }
    // dbg!(&table);
    table
}


type Foo = (Term, Term);

#[derive(Debug, PartialEq, Eq, PartialOrd, Ord, Hash, Clone)]
/*
    reduce_nf: (u32, Term, u32) = (reduce_limit, display_term, display_steps)
*/
struct UnsolvedData {reduce_nf: Option<(u32, Term, u32)>}

#[derive(Debug, PartialEq, Eq, PartialOrd, Ord, Hash, Clone)]
enum TermRes {
    Unsolved(UnsolvedData),
    /*
    the normal form
    the number of steps to get there
    the size of the normal form
    */
    Reduced(Term, u32, u32),
    /*
    the start and end number of reduction steps that we reduced the term for that
    results in a loop
     */
    Looped(u32, u32),
    /*
    the start and end number of reduction steps, let the term reduced for those 
    step counts be S and E. then S is a nf-order-reducing subterm of E
     */
    Subset(u32, u32),
    /* 
    30 Aug 2025: I have no idea what this is and the code isn't called, yikes
      same date update: I still don't know what it is, but it is called ...
     */
    AdvSubset(u32, u32),
    /* 
    the depth of Dro
    the resulting term
    and the proof that the resulting term doesn't halt
     */
    DroNonhalt(u32, Term, Vec<ReductionSpec>, Box<TermRes>),
}
use TermRes::*;

fn nf_reduce_one_term(term: Term, reduce_limit: u32, size_limit: u32, display_steps: u32)
-> (Term, TermRes) {
  let (red_term, steps, size_limit_reached) = nf_reduce(&term, reduce_limit, size_limit);
  if steps == reduce_limit || size_limit_reached {
      // we failed
      let (display_term, display_steps_used, size_limit_display_reached) = nf_reduce(&term, display_steps, size_limit);
      assert!((display_steps_used == display_steps) || size_limit_display_reached);
      (term, Unsolved(UnsolvedData { reduce_nf: Some((reduce_limit, display_term, display_steps_used)) }))
  } else {
      // normal form found
      let term_size = term_size(&red_term);
      (term, Reduced(red_term, steps, term_size))
  }
}

/*
attempt to reduce all terms to normal form. 
return value: the original term, plus the output TermRes. 
the output is Unsolved if no normal form was found, and gives the term reduced for the max steps in the option
the output is Reduced if a normal form was found
*/
fn reduce_list_of_terms(terms: Vec<Term>, reduce_limit: u32, size_limit: u32, display_steps: u32) 
    -> Vec<(Term, TermRes)>
{
    let mut out = vec![];
    for term in terms {
        // println!("size {} reducing {}", term_size(&term), print_term(&term));
        out.push(nf_reduce_one_term(term, reduce_limit, size_limit, display_steps))
    }
    out
}

// loop length is the difference between slow and fast when looped
// loop found by is the steps slow had taken by then
fn find_min_loop(term: Term, loop_length: u32, loop_found_by: u32) -> (Term, TermRes) {
    let orig_term = term.clone();
    // dbg!(print_term(&orig_term), loop_length, loop_found_by);
    let mut slow_term = term.clone();
    let mut fast_term = term; 
    for _fast_index in 0..loop_length {
        // println!("fast {}", fast_index);
        fast_term = nf_reduce_step(fast_term).expect("term should reduce");
    }
    if slow_term == fast_term {
        return (orig_term, Looped(0, loop_length))
    }
    for slow_index in 1..=loop_found_by {
        // println!("slow {}", slow_index);
        // println!("slow {} {}\nfast {} {}", term_size(&slow_term), print_term(&slow_term), term_size(&fast_term), print_term(&fast_term));
        slow_term = nf_reduce_step(slow_term).expect("slow should reduce");
        fast_term = nf_reduce_step(fast_term).expect("fast should reduce");
        if slow_term == fast_term {
            return (orig_term, Looped(slow_index, slow_index + loop_length))
        }
    
    }
    panic!("loop was found but no min loop was found: {}", print_term(&orig_term))
}

fn check_loop(term: Term, ud: UnsolvedData, loop_base: u32, loop_limit: u32) -> (Term, TermRes) {
    let orig_term = term.clone();
    let mut compare_term = term.clone();
    let mut red_term = nf_reduce_step(term)
        .expect("loop limit should be smaller than reduce limit");
    let mut prev_step_goal = 0;
    let mut next_step_goal = loop_base; 

    // step count is now 1 
    for step_count in 1..loop_limit {
        if red_term == compare_term {
            return find_min_loop(orig_term, 
                step_count-prev_step_goal, prev_step_goal);
        }
        if step_count == next_step_goal {
            compare_term = red_term.clone();
            prev_step_goal = next_step_goal;
            next_step_goal *= 2;
        }
        red_term = nf_reduce_step(red_term)
            .expect("loop limit should be smaller than reduce limit");
    }
    (orig_term, Unsolved(ud))
}

fn check_loop_wrap((term, prev_res): (Term, TermRes), loop_base: u32, loop_limit: u32) -> (Term, TermRes) {
  match prev_res {
    Reduced(_, _, _) => (term, prev_res),
    Unsolved(ud) => check_loop(term, ud, loop_base, loop_limit),
    // todo: fix these dumb match arms
    _ => panic!("unexpected 1"),
  }
}

fn check_loops(terms: Vec<(Term, TermRes)>, loop_base: u32, loop_limit: u32) -> Vec<(Term, TermRes)> {
    let mut out = vec![];
    for pair in terms {
      out.push(check_loop_wrap(pair, loop_base, loop_limit))
    }
    out
} 

#[derive(Debug, PartialEq, Eq, PartialOrd, Ord, Clone, Hash)]
enum TermWithIdR {
    Lambda(Box<TermWithId>),
    App(Box<TermWithId>, Box<TermWithId>),
    Index(u8)
}

#[derive(Debug, PartialEq, Eq, PartialOrd, Ord, Clone, Hash)]
struct TermWithId {id: Option<u64>, term: TermWithIdR}

// fn get_id(twi: &TermWithId) -> Option<u64> {
//     match twi {
//         TermWithId::Lambda(id, _) => *id,
//         TermWithId::App(id, _, _) => *id,
//         TermWithId::Index(id, _) => *id,
//     }
// }

fn twi_to_term(twi: TermWithId) -> Term {
    match twi {
        TermWithId {term: TermWithIdR::Lambda(sub_twi), .. } => Lambda(Box::new(twi_to_term(*sub_twi))),
        TermWithId {term: TermWithIdR::App(left_twi, right_twi) , ..} 
            => App(Box::new(twi_to_term(*left_twi)), Box::new(twi_to_term(*right_twi))),
        TermWithId {term: TermWithIdR::Index(n), .. } => Index(n),
    }
}

fn term_to_twi(term: Term) -> TermWithId {
    let id = term_to_u64(&term);
    let twir = match term {
        Lambda(subterm) => TermWithIdR::Lambda(Box::new(term_to_twi(*subterm))),
        App(left_term, right_term) => TermWithIdR::App(Box::new(term_to_twi(*left_term)), Box::new(term_to_twi(*right_term))),
        Index(n) => TermWithIdR::Index(n),
    };
    TermWithId { id, term: twir }
}

fn twi_lambda(twi: TermWithId) -> TermWithId {
    let id = term_to_u64(&Lambda(Box::new(twi_to_term(twi.clone()))));
    TermWithId { id, term: TermWithIdR::Lambda(Box::new(twi)) }
}

fn twi_app(left_twi: TermWithId, right_twi: TermWithId) -> TermWithId {
    let normal_term = App(Box::new(twi_to_term(left_twi.clone())), Box::new(twi_to_term(right_twi.clone())));
    let id = term_to_u64(&normal_term);
    TermWithId { id, term: TermWithIdR::App(Box::new(left_twi), Box::new(right_twi)) }
}

fn twi_index(n: u8) -> TermWithId {
    let id = term_to_u64(&Index(n));
    TermWithId { id, term: TermWithIdR::Index(n) }
}

fn re_de_bruijn_substituent_recur_twi(body_level: u8, substituent: &TermWithId, substituent_level: u8) -> TermWithId {
    assert!(body_level > 0);
    if body_level == 1 { 
        return substituent.clone() 
    };
    match &substituent.term {
        TermWithIdR::Index(n) => 
            if *n > substituent_level {twi_index(n + body_level - 1)} else {twi_index(*n)},
        TermWithIdR::Lambda(x) => 
            twi_lambda(
                re_de_bruijn_substituent_recur_twi(body_level, &x, substituent_level+1)
            ),
        TermWithIdR::App(x, y) => 
            twi_app(re_de_bruijn_substituent_recur_twi(body_level, &x, substituent_level),
                re_de_bruijn_substituent_recur_twi(body_level, &y, substituent_level)
            ),
    }
}

fn re_de_bruijn_substituent_twi(level: u8, substituent: &TermWithId) -> TermWithId {
    re_de_bruijn_substituent_recur_twi(level, substituent, 0)
}

fn substitute_level_twi(body: TermWithId, substituent: &TermWithId, level: u8) -> TermWithId {
    match body.term {
        TermWithIdR::Index(n) => {
            if n == level {
                re_de_bruijn_substituent_twi(level, substituent)
            } else if n > level {
                // in something like λ6, we need to take into account that there is 
                // one fewer lambda between the variable and its target now
                assert!(n != 1); //, "body {} substi {} level {}", print_term(&body), print_term(&substituent), level);
                twi_index(n-1)
            } else {
                // whereas in something like λλλ1, we don't need to change the 1
                twi_index(n) 
            }
        },
        TermWithIdR::Lambda(x) => twi_lambda(substitute_level_twi(*x, substituent, level+1)),
        TermWithIdR::App(x, y) => 
            twi_app(substitute_level_twi(*x, substituent, level), 
                substitute_level_twi(*y, substituent, level))
    }
}


// if you have a term like (λT) S then body is T and substituent is S 
fn substitute_twi(body: TermWithId, substituent: &TermWithId) -> TermWithId {
    // dbg!(format!("substituting {} into {}", print_term(substituent), print_term(&body)));
    let ans = substitute_level_twi(body, &substituent, 1);
    // dbg!(format!("ans: {}", print_term(&ans)));
    ans
}


// weak head normal form, E := (\x -> term) or (x term_1 . . . term_n)
// returns none if there is no reduction
// the idea is whenever we try to reduce a subterm, we check if that id is already 
// in the hashmap. if so we have hit a subterm-loop and we abort the whole reduction
// 
fn whnf_reduce_step_check_subset(term: TermWithId, hm: &HashMap<u64, u32>, cur_step: u32) -> Result<Option<TermWithId>, (u32, u32)> {
    if let Some(cur_id) = term.id {
        if let Some(&prev_step) = hm.get(&cur_id) {
            // what we have here is a subset proof
            return Err((prev_step, cur_step));
        }
    }
    
    match term.term {
        TermWithIdR::Lambda(_) => Ok(None),
        TermWithIdR::Index(_) => Ok(None),
        TermWithIdR::App(x, y) => {
            // we might need to reduce two things. first, reduce x to whnf. second, 
            // if that x is a lambda, then we need to substitute. 
            if let Some(x_reduced) = whnf_reduce_step_check_subset(*x.clone(), hm, cur_step)? {
                Ok(Some(twi_app(x_reduced, *y)))
            } else {
                match x.term {
                    TermWithIdR::App(_, _) => Ok(None),
                    TermWithIdR::Index(_) => Ok(None),
                    TermWithIdR::Lambda(z) => Ok(Some(substitute_twi(*z, &y))),
                }
            }
        },
    }
}

// normal form, ie E = (\x. E) or x E_1 . . . E_n
// returns None if there is no reduction
fn nf_reduce_step_check_subset(term: TermWithId, hm: &HashMap<u64, u32>, cur_step: u32) -> Result<Option<TermWithId>, (u32, u32)> {
    if let Some(cur_id) = term.id {
        if let Some(&prev_step) = hm.get(&cur_id) {
            // what we have here is a subset proof
            return Err((prev_step, cur_step));
        }
    }
        
    match term.term {
        TermWithIdR::Index(_) => Ok(None),
        TermWithIdR::Lambda(x) => 
            if let Some(new_term) = nf_reduce_step_check_subset(*x, hm, cur_step)? {
                Ok(Some(twi_lambda(new_term)))
            } else {
                Ok(None)
            },
        TermWithIdR::App(x, y) => {
            // first reduce x to whnf, if it becomes a lambda, then substitute. 
            // otherwise, reduce first x, then y to nf. 
            if let Some(x_reduced) = whnf_reduce_step_check_subset(*x.clone(), hm, cur_step)? {
                Ok(Some(twi_app(x_reduced, *y)))
            } else if let TermWithIdR::Lambda(z) = x.term {
                Ok(Some(substitute_twi(*z, &y)))
            } else if let Some(x_reduced) = nf_reduce_step_check_subset(*x.clone(), hm, cur_step)? {
                Ok(Some(twi_app(x_reduced, *y)))
            } else if let Some(y_reduced) = nf_reduce_step_check_subset(*y.clone(), hm, cur_step)? {
                Ok(Some(twi_app(*x, y_reduced)))
            } else {
                Ok(None)
            }
        },
    }
}

// Ok(term after reduction, steps of reduction)
// Err(start, end) // for subset proof
fn nf_reduce_twi(term: &TermWithId, reduce_limit: u32, hm: &HashMap<u64, u32>, cur_step: u32) 
    -> Result<(TermWithId, u32), (u32, u32)> 
{
    let mut counter = 0;
    let mut cur_term = term.clone();
    while let Some(reduced_term) = nf_reduce_step_check_subset(cur_term.clone(), hm, cur_step)? {
        cur_term = reduced_term;
        counter += 1;
        if counter == reduce_limit {
            break
        }
    }
    Ok((cur_term, counter))
}

/*  
the goal is to check whether on step n, we try to reduce as a subterm the entire 
term that we were trying to reduce on step k < n
*/
fn check_subset_term(term: Term, ud: UnsolvedData, check_limit: u32) -> (Term, TermRes) {
    let orig_term = term.clone();
    let mut cur_term = term_to_twi(term.clone());
    let mut hm = HashMap::new();
    for step in 0..check_limit {
        let mb_cur_id = cur_term.id;

        // TODO: either implement or remove this
        // if let Some(prev_step) = hm.insert(cur_id, step) {
        //     // we have already seen the full top level term, so this is a loop
        //     return find_min_loop(orig_term, step - prev_step, prev_step);
        // }

        cur_term = match nf_reduce_step_check_subset(cur_term, &hm, step) {
            Ok(None) => return (orig_term, Unsolved(ud)),
            Ok(Some(red_term)) => red_term,
            Err((start, end)) => return (orig_term, Subset(start, end)),
        };
        if let Some(cur_id) = mb_cur_id {
            hm.insert(cur_id, step);
        }
    }
    return (orig_term, Unsolved(ud))
}

fn check_subset_terms(terms: Vec<(Term, TermRes)>, check_limit: u32) -> Vec<(Term, TermRes)> {
    let mut out = vec![];
    for (term, prev_res) in terms {
        match prev_res {
            // todo: fix these dumb match arms
            Reduced(_, _, _) => out.push((term, prev_res)),
            Looped(_, _) => out.push((term, prev_res)),
            Unsolved(ud) => {
                let ans = check_subset_term(term.clone(), ud.clone(), check_limit);
                match ans.1 {
                    Subset(s, e) => {
                        let ans2 = nf_reduce_all_subsets(term.clone(), ud, check_limit);
                        assert_eq!(ans2.1, AdvSubset(s, e), "failed on term {}", print_term(&term));
                    }
                    _ => (),
                }
                out.push(ans);
            },
            _ => panic!("unexpected 2"),
        }
    }
    out
} 


//returns prev_step if known 
fn hist_contains(history: &[Vec<(Term, u32)>], term: &Term) -> Option<u32> {
    for level_hist in history {
        for (prev_term, step) in level_hist {
            if prev_term == term {
                return Some(*step);
            }
        }
    };
    None
}

fn whnf_reduce_all_subsets_step(
    term: Term, history: &mut Vec<Vec<(Term, u32)>>, level: usize, cur_step: u32
) -> Result<Option<Term>, TermRes>
{
    // println!("w {} {}", level, print_term(&term));

    // check if the history contains the current term up to this level; if so return nonhalt
    if let Some(prev_step) = hist_contains(&history[0..level], &term) {
        return Err(AdvSubset(prev_step, cur_step));
    };
    // add the current term to the history at the right level
    while history.len() <= level {
        history.push(vec![]);
    };
    history[level].push((term.clone(), cur_step));
    
    // perform one step of whnf_reduction
    match term {
        Index(_) => {
            history.truncate(level); 
            Ok(None)
        },
        Lambda(_) => {
            history.truncate(level); 
            Ok(None)
        },
        App(l, r) => match *l {
            Lambda(body) => {
                // println!("subbing into {} with {}", print_term(&body), print_term(&r));
                Ok(Some(substitute(*body, &r)))
            },
            l => match whnf_reduce_all_subsets_step(l, history, level+1, cur_step)? {
                None => Ok(None),
                Some(l_reduced) => Ok(Some(App(Box::new(l_reduced), r))),
            }
        },
    }
}

fn nf_reduce_all_subsets_step(
    term: Term, history: &mut Vec<Vec<(Term, u32)>>, level: usize, cur_step: u32
) -> Result<Option<Term>, TermRes> 
{
    // println!("{} {}", level, print_term(&term));
    // check if the history contains the current term up to this level; if so return nonhalt
    if let Some(prev_step) = hist_contains(&history[0..level], &term) {
        return Err(AdvSubset(prev_step, cur_step));
    };
    // add the current term to the history at the right level
    while history.len() <= level {
        history.push(vec![]);
    };
    history[level].push((term.clone(), cur_step));

    // perform one step of nf_reduction
    match term {
        Index(_) => Ok(None),
        Lambda(sub_term) => 
        if let Some(new_term) = nf_reduce_all_subsets_step(*sub_term, history, level+1, cur_step)? {
            Ok(Some(Lambda(Box::new(new_term))))
        } else {
            history.truncate(level);
            Ok(None)
        },
        App(l, r) => 
        if let Some(l_reduced) = whnf_reduce_all_subsets_step(*l.clone(), history, level+1, cur_step)? {
            Ok(Some(App(Box::new(l_reduced), r)))
        } else if let Lambda(z) = *l {
            // println!("subbing into {} with {}", print_term(&z), print_term(&r));
            Ok(Some(substitute(*z, &r)))
        } else if let Some(l_reduced) = nf_reduce_all_subsets_step(*l.clone(), history, level+1, cur_step)? {
            Ok(Some(App(Box::new(l_reduced), r)))
        } else if let Some(r_reduced) = nf_reduce_all_subsets_step(*r, history, level+1, cur_step)? {
            Ok(Some(App(l, Box::new(r_reduced))))
        } else {
            history.truncate(level);
            Ok(None)
        },
    }
}

fn nf_reduce_all_subsets(term: Term, ud: UnsolvedData, check_limit: u32)  -> (Term, TermRes) {
  // the goal of this function is to reduce a term to normal form, but keep track of all of the 
  // subterms we're aiming to reduce during that. if we ever notice we're trying to reduce a 
  // subterm that is the same as a subterm we were already in the middle of trying to reduce, 
  // we can be sure we will never finish 
    let orig_term = term.clone();
    let mut current_term = term;

//     println!("\nsolving {}", print_term(&orig_term));
    let mut history = vec![];
    for cur_step in 0..check_limit {
        let prev_term = current_term.clone();
        // println!("\nreducing {} {}", cur_step, print_term(&current_term));
        current_term = match nf_reduce_all_subsets_step(current_term, &mut history, 0, cur_step) {
            Ok(None) => panic!{"subsets limit should be smaller than red limit {} {}", print_term(&orig_term), print_term(&prev_term)},
            Ok(Some(new_term)) => new_term,
            Err(nonhalt_proof) => return (orig_term, nonhalt_proof),
        };
    }
    (orig_term, Unsolved(ud))
}

fn check_all_subset((term, prev_res): (Term, TermRes), check_limit: u32) -> (Term, TermRes) {
  match prev_res {
    // todo: fix these dumb match arms
    Reduced(_, _, _) => (term, prev_res),
    Looped(_, _) => (term, prev_res),
    Unsolved(ud) => nf_reduce_all_subsets(term, ud, check_limit),
    _ => panic!("unexpected 3"),
  }
}
fn check_all_subset_terms(terms: Vec<(Term, TermRes)>, check_limit: u32) -> Vec<(Term, TermRes)> {
    let mut out = vec![];
    for pair in terms {
      out.push(check_all_subset(pair, check_limit))
    }
    out

}

// implementation of DRO (Different Reduction Order) starts here
/* 
  the idea, is that a term may have many available beta reductions. 
  only the "leftmost outermost", the NF-reduction, is guaranteed to progress 
  towards a halting state, if such a state exists. however, if a halting state 
  exists, then any possible beta reduction will take you to a term with the same
  halting state. 

  therefore, a valid proof of halting could end up much shorter if you take reductions
  in a different order. (this isn't yet relevant to us, since we currently solve up 
  to 23 bit terms, and all unsolved terms for 24-27 (1,3,1,4) = 9 total) are 
  nonhalting. 

  importantly, however, if you can perform some arbitrary sequence of reductions, 
  then show the resulting term does not halt, the original term must not have 
  halted. This solves all 9 holdouts up to size 27 AFAICT (I don't currently 
  know any (!!) counterexample to this method, though I imagine it isn't way bigger
  than 28. 30 would be a little lucky, 32 would be pretty lucky, higher than that is 
  hard to believe). 

  architecture: 
  1. a function which takes a lambda term and returns it reduced by all possible reductions. 
  for ease of correctness, this function will also return the pair of subterms that were
  reduced by one step, and a path from the top level to the place a subterm was reduced. 
  2. a function which takes a lambda term and a depth and uses (1) to compute all sequences
  of reduction at that depth (avoiding duplicates) 
  3. a function which takes a lambda term, and a maximum depth, and iterates from depth 1 to
  the maximum depth, computes all possible terms at that depth, then runs those through the 
  currently known nonhalting deciders. then assembles any proof into a nice certificate. 
*/

#[derive(Debug, PartialEq, Eq, PartialOrd, Ord, Hash, Clone)]
enum SubLoc {
  LambdaD, //down
  AppL(Term), // the term is left, so we keep a pointer to the right
  AppR(Term), // and vv 
}
/*
 the global term after reduction, 
 the pre-reduction subterm that was selected, and 
 the path from the root of the term to the location of the selected subterm
 */ 
#[derive(Debug, PartialEq, Eq, PartialOrd, Ord, Hash, Clone)]
struct ReductionSpec {new_term: Term, reduced_subterm: Term, subterm_location: Vec<SubLoc>}

fn raise_spec_level(
  ReductionSpec { new_term, reduced_subterm, mut subterm_location }: ReductionSpec,
  sub_loc: SubLoc
) -> ReductionSpec {
  subterm_location.push(sub_loc.clone());
  match sub_loc {
    SubLoc::LambdaD => 
    ReductionSpec { new_term: Lambda(Box::new(new_term)), reduced_subterm, subterm_location },
    SubLoc::AppL(right_term) => 
      ReductionSpec { new_term: App(Box::new(new_term), Box::new(right_term.clone())), reduced_subterm, subterm_location },
    SubLoc::AppR(left_term) => 
      ReductionSpec { new_term: App(Box::new(left_term.clone()), Box::new(new_term)), reduced_subterm, subterm_location },
  }
  
}

fn raise_all_spec_level<'a>(specs: Vec<ReductionSpec>, sub_loc: SubLoc) -> Vec<ReductionSpec> {
  specs.into_iter().map(|spec|raise_spec_level(spec, sub_loc.clone())).collect()
}

fn all_reductions_of_term(term: &Term) -> Vec<ReductionSpec> {
  match term {
    Index(_) => vec![], 
    Lambda(x) => {
      let level_down_specs = all_reductions_of_term(x); 
      raise_all_spec_level(level_down_specs, SubLoc::LambdaD)
    }, 
    App(x, y) => {

      let mut all_specs = vec![];
      if let Lambda(z) = *x.clone() {
        let reduced_term = substitute(*z, &y);
        let top_level_spec = ReductionSpec {
          new_term: reduced_term,
          reduced_subterm: term.clone(), 
          subterm_location: vec![],
        };
        all_specs.push(top_level_spec);
      }
      let x_specs = raise_all_spec_level(all_reductions_of_term(x), SubLoc::AppL(*y.clone()));
      let y_specs = raise_all_spec_level(all_reductions_of_term(y), SubLoc::AppR(*x.clone()));
      all_specs.extend(x_specs);
      all_specs.extend(y_specs);
      all_specs
    }, 
  }
}

// a list, where each term in the list, is the reduced term, 
// plus a list of RS that got you there
fn arbitrary_reductions_of_depth(term: &Term, depth: u32) 
  -> Vec<(Term, Vec<ReductionSpec>)> 
{
  let mut out = vec![(term.clone(), vec![])];
  for _d in 0..depth {
    let mut new_out = vec![];
    // reduce everything by one more
    for (term, reduction_sequence) in out.iter() {
      let reds = all_reductions_of_term(&term);
      for red in reds {
        let new_term = red.new_term.clone();
        let mut new_seq = reduction_sequence.clone();
        new_seq.push(red);
        new_out.push((new_term, new_seq))
      }
    }
    // now dedup 
    new_out = new_out.iter().unique_by(|(t, _)| t).cloned().collect();
    out = new_out;
  }
  out 
}

fn attempt_solve_term(term: Term) -> TermRes {
  let nf_res = nf_reduce_one_term(term, 50, 100_000, 10);
  let loop_res = check_loop_wrap(nf_res, 10, 40);
  let subset_res = check_all_subset(loop_res, 20);
  subset_res.1
}

fn dro_term(original_term: &Term, ud: UnsolvedData, max_depth: u32) -> (Term, TermRes) {
  let mut prev_seen_terms = HashSet::new();
  prev_seen_terms.insert(original_term.clone());
  for depth in 1..=max_depth {
    let possible_terms = arbitrary_reductions_of_depth(original_term, depth);
    let unseen_terms = possible_terms.into_iter()
      .filter(|t|!prev_seen_terms.contains(&t.0));
    for (term, rs) in unseen_terms {
      match attempt_solve_term(term.clone()) {
        Unsolved(_) => (), 
        solved => {
          let term_res = DroNonhalt(depth, term, rs, Box::new(solved));
          return (original_term.clone(), term_res)
        }
      }
    }
  }
  return (original_term.clone(), Unsolved(ud))
}

fn dro_all_terms(terms: Vec<(Term, TermRes)>, max_depth: u32) -> Vec<(Term, TermRes)> {
  let mut out = vec![];
  for (term, prev_res) in terms {
    match prev_res {
      DroNonhalt(_, _, _, _) => panic!("unexpected 4"),
      Unsolved(ud) => out.push(dro_term(&term, ud, max_depth)),
      _ => out.push((term, prev_res)),
    }
  }
  out
}

// end DRO 

fn print_term(term: &Term) -> String {
    let switch = true;
    if switch {
        match term {
            Index(n) => n.to_string(),
            Lambda(x) => "λ".to_owned() + &print_term(x),
            App(x, y) => format!("({}){}", print_term(x), print_term(y)),
        }
    } else {
        match term {
            Index(n) => n.to_string(),
            Lambda(x) => "λ".to_owned() + &print_term(x),
            App(x, y) => format!("A{}{}", print_term(x), print_term(y)),
        }
    }
}

fn print_term_reduction(term: &Term, reduce_steps: u32) -> String {
    let mut out = String::new();
    let mut cur_term = term.clone();
    for step in 0..reduce_steps {
        out.push_str(&format!("step {} size {} term {}\n", step, term_size(&cur_term), print_term(&cur_term)));
        cur_term = match nf_reduce_step(cur_term) {
            None => return out,
            Some(t) => t,
        }
    }
    out 
}

fn print_terms(terms: &[Term]) -> String {
    let mut out = String::new();
    out.push('[');
    for term in terms {
        out.push_str(&print_term(term));
        out.push_str(&", ")
    }
    out.push(']');
    out
}

fn print_term_refs(terms: &[&Term]) -> String {
    let mut out = String::new();
    out.push('[');
    for term in terms {
        out.push_str(&print_term(term));
        out.push_str(&", ")
    }
    out.push(']');
    out
}

fn display_solved_term(t: &Term, r: &Term, steps: u32, size: u32) {
    println!("{} reduced to {} in {} steps (output size: {})", print_term(t), print_term(r), steps, size)
}

fn display_unsolved_term(t: &Term, r: &Term, display_steps: u32) {
    println!("{} reduced to {} (not in normal form) in {} steps", print_term(t), print_term(r), display_steps)
}

fn display_looped_term(t: &Term, s: u32, e: u32) {
    println!("{} looped from {} to {}", print_term(t), s, e);
}

fn display_subset_term(t: &Term, s: u32, e: u32) {
    println!("{} subset from {} to {}", print_term(t), s, e);
}

fn display_dro_term(t: &Term, depth: u32, reduced_term: &Term, proof: Box<TermRes>) {
  println!("{} original, depth {} reduced to {} which was solved by {:?}", 
            print_term(t), depth, print_term(reduced_term), proof);
}

// if a duplicate exists, returns it
fn find_duplicate<H: Hash + Eq>(objs: &Vec<H>) -> Option<&H> {
    let mut hs = HashSet::new();
    for obj in objs {
        if !hs.insert(obj) {
            return Some(obj);
        }
    }
    return None;
}

fn display_output(red_output: Vec<(Term, TermRes)> , step_limit: u32, display_steps: u32) {
    let total_len = red_output.len();
    
    // split into solved and holdouts 
    let mut nf_terms = vec![];
    let mut loop_terms = vec![];
    let mut subset_terms = vec![];
    let mut dro_terms = vec![];
    let mut unsolved = vec![];
    for output in red_output {
        match output {
            (t, Unsolved(UnsolvedData{reduce_nf: Some((_, r, _))})) => unsolved.push((t, r)),
            (_t, Unsolved(UnsolvedData{reduce_nf: None})) => panic!("no unsolved data"),
            (t, Reduced(r, steps, size)) => nf_terms.push((t, r, steps, size)),
            (t, Looped(loop_start, loop_end)) => loop_terms.push((t, loop_start, loop_end)),
            (t, Subset(start, end)) => subset_terms.push((t, start, end)),
            (t, AdvSubset(start, end)) => subset_terms.push((t, start, end)),
            (t, DroNonhalt(depth, dro_term, rs, proof)) => dro_terms.push((t, depth, dro_term, rs, proof)),

        }
    }

    let num_solved = nf_terms.len() + loop_terms.len() + subset_terms.len() + dro_terms.len();
    let num_unsolved = unsolved.len(); 
    assert_eq!(num_solved + num_unsolved, total_len);

    println!("There were {} terms, of which {} were solved and {} were unsolved", 
        total_len, num_solved, unsolved.len());
    if loop_terms.len() > 0 {
        println!("\n{} terms were solved by looping", loop_terms.len());
        let mut sorted_by_end = loop_terms.clone();
        sorted_by_end.sort_by_key(|(_t, _s, e)| *e);
        sorted_by_end.reverse();
        for (t, s, e) in &sorted_by_end[0..10.min(sorted_by_end.len())] {
            display_looped_term(t, *s, *e);
        }
    }

    if subset_terms.len() > 0 {
        println!("\n{} terms were solved by subsets", subset_terms.len());
        let mut sorted_by_end = subset_terms.clone();
        sorted_by_end.sort_by_key(|(_t, _s, e)| *e);
        sorted_by_end.reverse();
        for (t, s, e) in &sorted_by_end[0..10.min(sorted_by_end.len())] {
            display_subset_term(t, *s, *e);
        }
    }

    if dro_terms.len() > 0 {
      println!("\n{} terms were solved by DRO", dro_terms.len()); 
      let mut sorted_by_depth = dro_terms.clone(); 
      sorted_by_depth.sort_by_key(|tup| tup.1); 
      sorted_by_depth.reverse(); 
      for (t, depth, reduced_term, _rs, proof) in sorted_by_depth {
        display_dro_term(&t, depth, &reduced_term, proof);
      }
    }

    if nf_terms.len() > 0 {
    // show maximum reduction steps
    let mut sorted_by_steps = nf_terms.clone();
    sorted_by_steps.sort_by_key(|(_t, _r, steps, _size)|*steps);
    sorted_by_steps.reverse();
    println!("\nmaximum reduction steps: {}", sorted_by_steps[0].2);
    // and three such longest terms
    for (t, r, steps, size) in &sorted_by_steps[0..3.min(sorted_by_steps.len())] {
        display_solved_term(t, r, *steps, *size)
    }

    // show maximum output size
    let mut sorted_by_size = nf_terms.clone();
    sorted_by_size.sort_by_key(|(_t, _r, _steps, size)|*size);
    sorted_by_size.reverse();
    println!("maximum output size: {}", sorted_by_size[0].3);
    // and three such largest terms 
    for (t, r, steps, size) in &sorted_by_size[0..3.min(sorted_by_size.len())] {
        display_solved_term(t, r, *steps, *size)
    }
    }

    // display number of holdouts
    println!("\nThere were {} unsolved terms", unsolved.len());
    println!("All were reduced for {} steps without finding a normal form, but only {} steps are displayed.", 
        step_limit, display_steps);
    // display some holdouts
    for (t, r) in &unsolved[0..10.min(unsolved.len())] {
        display_unsolved_term(t, r, display_steps);
    }
}

#[derive(Debug)]
enum Token {
    Lambda, 
    Open, 
    Close,
    Index(u8)
}

fn tokenize(term_string: String) -> Vec<Token> {
    let mut out = Vec::new();
    for s in term_string.chars() {
        match s {
            'λ' => out.push(Token::Lambda),
            '(' => out.push(Token::Open), 
            ')' => out.push(Token::Close),
            c => {
                if c.is_ascii_digit() && c != '0' {
                    out.push(Token::Index(c.to_digit(10).expect("we checked it is a digit") as u8))
                } else {
                    panic!("passed invalid charaacter {}", c)
                }
            }
        }
    }
    out
}

fn parse_tokens_recur(tokens: &[Token]) -> Option<(Term, &[Token])> {
    let first_token = tokens.first().expect("no parsing empty tokens");
    match first_token {
        Token::Lambda => {
            if tokens.len() == 1 {
                None
            } else {
                let (rest_term, rest_tokens) = parse_tokens_recur(&tokens[1..])?;
                Some((Lambda(Box::new(rest_term)), rest_tokens))
            }
        },
        Token::Index(n) => {
            Some((Index(*n), &tokens[1..]))
        },
        Token::Open => {
            let (term_a, rest_tokens) = parse_tokens_recur(&tokens[1..])?;
            if let Some(Token::Close) = rest_tokens.first() {
                let (term_b, rest_tokens) = parse_tokens_recur(&rest_tokens[1..])?;
                Some((App(Box::new(term_a), Box::new(term_b)), rest_tokens))
            } else {
                None
            }
        },
        Token::Close => None,
    }
}

fn parse_tokens(tokens: &[Token]) -> Option<Term> {
    let (term, rest_tokens) = parse_tokens_recur(tokens)?;
    if rest_tokens.len() == 0 {
        Some(term) 
    } else {
        None
    }

}

//for now only works up to 9 de-bruijn, higher things could be done at some point
fn parse_term(term_string: String) -> Option<Term> {
    parse_tokens(&tokenize(term_string))
}

fn main() {
    let max_size = 28;
    let step_limit = 50;
    let size_limit = 100_000;
    let display_steps = 10;
    let table = dp_list_terms_of_size_open(max_size, 0);
    for size in 0..=max_size {
        println!("\n\n\nsize: {}", size);
        let input = table[size][0].clone();
        println!("num terms: {}", input.len());
        if let Some(duplicate) = find_duplicate(&input) {
            panic!("size {} duplicate term {}\nall terms: {}", size, print_term(duplicate), print_terms(&input));
        }
        let red_terms = reduce_list_of_terms(input, step_limit, size_limit, display_steps);
        println!("terms red");
        let loop_terms = check_loops(red_terms, 10, 40);
        println!("terms loop");
        let subset_terms = check_all_subset_terms(loop_terms, 20);
        println!("terms subset");
        let dro_terms = dro_all_terms(subset_terms, 4);
        let output = dro_terms;
        display_output(output, step_limit, display_steps);
    }

    // let term = parse_term("λ((λ(1)1)λ(1)(λ1)1)1".to_owned()).unwrap();
    // println!("{}", print_term_reduction(&term, 10));
    // nf_reduce_all_subsets(term, UnsolvedData { reduce_nf: None }, 10);

    let term = parse_term("(λ(1)1)λ(1)(λ1)1".to_owned()).unwrap();
    println!("{}", print_term_reduction(&term, 10));

    // the next thing to do is DRO - "different reduction order" 
    // you first reduce for some number 1 . . . k steps trying all possible reductions
    // then you apply previous deciders & if they prove the new term does or does not halt, then the 
    // original term has the same property 

    // also this is a bug: 
    //size 24  There were 8574 terms, of which 8569 were solved and 1 were unsolved

}

mod test {
    use super::*;
    
    fn t_str(s: &str) -> Term {
        parse_term(s.to_owned()).unwrap()
    }

    fn id() -> Term {
        Lambda(Box::new(Index(1)))
    }

    fn zero() -> Term {
        Lambda(Box::new(Lambda(Box::new(
            Index(1)
        ))))
    }

    fn one() -> Term {
        Lambda(Box::new(Lambda(Box::new(
            App(Box::new(Index(2)), Box::new(Index(1)))
        ))))
    }

    #[test]
    fn terms_print() {
        let id = Lambda(Box::new(Index(1)));
        let one = Lambda(Box::new(Lambda(Box::new(App(Box::new(Index(2)), Box::new(Index(1)))))));
        
        let id_str = "λ1";
        let one_str = "λλ(2)1";

        assert_eq!(print_term(&id), id_str);
        assert_eq!(print_term(&one), one_str);
    }

    #[test]
    fn terms_parse_round_trip() {
        let id = Lambda(Box::new(Index(1)));
        let one = Lambda(Box::new(Lambda(Box::new(App(Box::new(Index(2)), Box::new(Index(1)))))));

        assert_eq!(parse_term(print_term(&id)), Some(id));
        assert_eq!(parse_term(print_term(&one)), Some(one));

        let two = "λλ(2)(2)1";
        assert_eq!(print_term(&parse_term(two.to_owned()).unwrap()), two);
        let three = "λλ(2)(2)(2)1";
        assert_eq!(print_term(&parse_term(three.to_owned()).unwrap()), three);
        let plus_part = "((3)2)1";
        assert_eq!(print_term(&parse_term(plus_part.to_owned()).unwrap()), plus_part);
        let plus = "λλλλ((4)2)((3)2)1";
        assert_eq!(print_term(&parse_term(plus.to_owned()).unwrap()), plus);
    }

    #[test]
    fn term_size_test() {
        let id = Lambda(Box::new(Index(1)));
        // one = λλA21
        let one = Lambda(Box::new(Lambda(Box::new(App(Box::new(Index(2)), Box::new(Index(1)))))));
        assert_eq!(term_size(&id), 4);
        assert_eq!(term_size(&one), 11);
        // 4 lambdas -> 8, then A A42 AA321 which is 4 As -> 8
        // 42 -> 4 + 4 = 8, 321 -> 6 + 3 = 9
        // 8 + 8 + 8 + 9 = 33
        let plus_str = "λλλλ((4)2)((3)2)1";
        let plus = parse_term(plus_str.to_owned()).unwrap();
        assert_eq!(term_size(&plus), 33);
    }

    #[test]
    fn term_openness_test() {
        assert_eq!(term_openness(&id()), 0);
        assert_eq!(term_openness(&one()), 0);
        assert_eq!(term_openness(&t_str("λ3")), 2);
        assert_eq!(term_openness(&t_str("λ4")), 3);
        assert_eq!(term_openness(&t_str("(1)(λλ3)λ1")), 1);
        assert_eq!(term_openness(&t_str("((((4)5)6)7)8")), 8);
    }
    
    #[test]
    fn term_closed_test() {
        assert_eq!(is_closed(&id()), true);
        assert_eq!(is_closed(&one()), true);
        assert_eq!(is_closed(&t_str("λ3")), false);
        assert_eq!(is_closed(&t_str("λ4")), false);
        assert_eq!(is_closed(&t_str("(1)(λλ3)λ1")), false);
        assert_eq!(is_closed(&t_str("((((4)5)6)7)8")), false);
    }

    #[test]
    fn term_counting_works() {
        let correct_ans = vec![0, 0, 0, 0, 1, //0 to 4
                                         0, 1, 1, 2, 1, //5 to 9
                                         6, 5, 13, 14, 37, //10 to 12 by hand, rest by calculation
                                         44, 101, 134, 298, 431, //15 to 19
                                         883, 1361, 2736, 4405, 8574, //20 to 24
                                         14334, 27465, 47146, 89270, 156360, //25 to 29
                                         293_840, 522_913, 978_447, 1_761_907, 3_288_605, //30 to 34
                                         5_977_863, 11_148_652, 20_414_058, 38_071_898, 70_125_402, //35 to 39
                                         130_880_047, 242_222_714, 452_574_468, 840_914_719, 1_573_331_752, //40 to 44
                                         2_933_097_201, 5_495_929_096, 10_275_069_737, 19_282_848_050, 36_140_122_614, //45 to 49
                                         67_928_087_938, 127_589_648_624, 240_179_940_582, 452_010_210_830, 852_138_794_150, //50 to 54
                                         1_606_513_707_059, 3_032_924_598_421, 5_727_034_034_907, 10_826_642_256_913, 20_473_798_909_321, //55 to 59
                                         38_754_322_685_329, 73_385_837_088_228, 139_079_361_409_127, 263_693_749_320_202, 500_323_417_424_622, //60 to 64
                                        ];
        let mut calculated_ans = vec![];
        for size in 0..correct_ans.len() {
            calculated_ans.push(dp_counting_terms_of_size_open(size, 0));
        }
        assert_eq!(correct_ans, calculated_ans);

    }


    #[test]
    fn test_nf_reduce() {
        let t = t_str(&"λ(λ2)λ1");
        let (nf_t, _, _) = nf_reduce(&t, 10, 1_000);
        let ans = t_str(&"λ1");
        assert_eq!(nf_t, ans);

        assert_eq!(nf_reduce(&t_str(&"λ(λ(2)1)1"), 10, 1_000).0, t_str(&"λ(1)1"));
        assert_eq!(nf_reduce(&t_str(&"λ(λ(1)2)1"), 10, 1_000).0, t_str(&"λ(1)1"));
        assert_eq!(nf_reduce(&t_str(&"λλ(λ1)λ3"), 10, 1_000).0, t_str(&"λλλ3"));
        assert_eq!(nf_reduce(&t_str(&"λλ(λ3)λ1"), 10, 1_000).0, t_str(&"λλ2"));
        assert_eq!(nf_reduce(&t_str(&"λ(λλ2)1"), 10, 1_000).0, t_str(&"λλ2"));
        assert_eq!(nf_reduce(&t_str(&"λλ(λλ2)2"), 10, 1_000).0, t_str(&"λλλ3"));
        assert_eq!(nf_reduce(&t_str(&"λ(λλ2)λ2"), 10, 1_000).0, t_str(&"λλλ3"));

        let x = t_str(&"λλλ(λ(λλ3)(1)2)(1)λ4");
        let x_red_1 = nf_reduce_step(x.clone()).unwrap();
        let x_red_1_str = print_term(&x_red_1);
        let (x_red, _steps, _) = nf_reduce(&x, 10, 1_000);
        // dbg!(steps);
        let x_red_str = print_term(&x_red);
        let y = t_str(&"λλλ(λλ(3)λ6)((1)λ4)1");
        let y_str = print_term(&y);
        let z = t_str(&"λλλλ(2)λ5");
        let z_str = print_term(&z);
        assert_eq!(x_red_1_str, y_str);
        assert_eq!(x_red_str, z_str);
        // assert_eq!(nf_reduce(t_str(&"λλλ(λ(λλ3)(1)2)(1)λ4")).0, 
        //                      t_str(&"λλλ(λλ(3)λ6)((1)λ4)1"));
    }

    #[test]
    fn test_enumerate_terms_of_size() {
        let table_to_16 = dp_list_terms_of_size_open(24, 0);
        for size in 0..=24 {
            let table_size = table_to_16[size][0].len();
            let ans = dp_counting_terms_of_size_open(size, 0);
            assert_eq!(table_size, ans.try_into().unwrap(), "size {}", size);
        }
    }
    /*
    functions to write:
        print term in a human readable way instead of de bruijn
        reduce terms, separate into holdouts and non-holdouts, etc. 
    tests still to write:
        substitute?
        whnf reduction?
     */


    #[test]
    fn test_bits_to_bytes() {
        let bits_zero = [false; 8];
        let byte = bit_array_to_byte(&bits_zero);
        assert_eq!(byte, 0);
        
        let bits_255 = [true; 8];
        let byte = bit_array_to_byte(&bits_255);
        assert_eq!(byte, 255);
        
        let bits_1 = [false, false, false, false,
                               false, false, false, true];
        let byte = bit_array_to_byte(&bits_1);
        assert_eq!(byte, 1);

        
        let bits_128 = [true, false, false, false,
                               false, false, false, false];
        let byte = bit_array_to_byte(&bits_128);
        assert_eq!(byte, 128);

        let bits_85 = [false, true, false, true,
                               false, true, false, true];
        let byte = bit_array_to_byte(&bits_85);
        assert_eq!(byte, 85);

        let mut bits_vec = vec![];
        bits_vec.extend(bits_85);
        bits_vec.extend(bits_1);
        bits_vec.extend(bits_1);
        bits_vec.extend(bits_255);
        bits_vec.extend(bits_128);
        let bytes_vec = bit_list_to_byte_list(bits_vec);
        let ans_vec = vec![85, 1, 1, 255, 128];
        assert_eq!(bytes_vec, ans_vec);
    }

    #[test]
    fn test_term_to_u64() {
        let id = Lambda(Box::new(Index(1)));
        let mb_u64 = term_to_u64(&id);
        // id should be 2 plus 16
        assert_eq!(mb_u64, Some(18));

        let dup = &t_str("λ(1)1");
        let mb_u64 = term_to_u64(&dup);
        // dup is λA11 so 0001 1010 which is 2 + 8 + 16 = 26
        // so as a u64 it'll be 26 + 256 = 282
        assert_eq!(mb_u64, Some(282)); 
    }


    fn check_terms_present_in_reductions(term: &Term, ans_terms: &[Term]) {
      assert!(ans_terms.iter().all_unique());
      let reductions = all_reductions_of_term(term);
      let found_terms: HashSet<Term> = reductions.into_iter().map(|rs|rs.new_term.clone()).unique().collect();
      assert_eq!(found_terms.len(), ans_terms.len()); 
      for ans in ans_terms {
        assert!(found_terms.contains(&ans));
      }
    }

    #[test] 
    fn test_all_reductions_of_term() {
      let terms_with_no_reductions = [id(), zero(), one()]; 
      for term in terms_with_no_reductions {
        let all_red = all_reductions_of_term(&term);
        assert_eq!(all_red.len(), 0, "{:?}", &all_red);
      }
      /* examples I want to exist: 
      the guy of size 24
      dup (dup dup)
      \x. (id x) (id x) (id x) 
      */

      // dup (\x. x (id x))
      // input is dup Y
      // output should be Y Y or dup dup 
      let dro_holdout = t_str("(λ(1)1)λ(1)(λ1)1");
      let ans_terms = [t_str("(λ(1)1)λ(1)1"), t_str("(λ(1)(λ1)1)λ(1)(λ1)1")];
      check_terms_present_in_reductions(&dro_holdout, &ans_terms);

      // dup (dup dup)
      // output is dup (dup dup) or (dup dup) (dup dup)
      let dup_of_dupdup = t_str("(λ(1)1)(λ(1)1)λ(1)1");
      let ans_terms = [dup_of_dupdup.clone(), t_str("((λ(1)1)λ(1)1)(λ(1)1)λ(1)1")];
      check_terms_present_in_reductions(&dup_of_dupdup, &ans_terms);
      // (dup dup) dup 
      // output is (dup dup) dup
      let dupdup_of_dup = t_str("((λ(1)1)λ(1)1)λ(1)1");
      let ans_terms = [dupdup_of_dup.clone()];
      check_terms_present_in_reductions(&dupdup_of_dup, &ans_terms);

      // \x. (id x) (id x) (id x) 
      // output is \x. x (id x) (id x) and so on (3) 
      // id x is (λ1)1
      let three_ids = t_str("λ(((λ1)1)(λ1)1)(λ1)1");
      let ans_terms = [t_str("λ((1)(λ1)1)(λ1)1"), t_str("λ(((λ1)1)1)(λ1)1"), t_str("λ(((λ1)1)(λ1)1)1")];
      check_terms_present_in_reductions(&three_ids, &ans_terms);
    }


    fn check_terms_present_in_depth_reductions(term: &Term, depth: u32, ans_terms: &[Term]) {
      assert!(ans_terms.iter().all_unique());
      let depth_reductions = arbitrary_reductions_of_depth(term, depth);
      let found_terms: HashSet<Term> = depth_reductions.into_iter()
        .map(|(term, _)|term)
        .unique().collect();
      assert_eq!(found_terms.len(), ans_terms.len()); 
      for ans in ans_terms {
        assert!(found_terms.contains(&ans), "{:?}", ans);
      }
    }

    #[test]
    fn test_arbitrary_reductions_of_depth() {
      let terms_with_no_reductions = [id(), zero(), one()]; 
      for term in terms_with_no_reductions {
        let zero_red = arbitrary_reductions_of_depth(&term, 0);
        assert_eq!(zero_red, vec![(term.clone(), vec![])]);
        for depth in 1..=3 {
          let d_red = arbitrary_reductions_of_depth(&term, depth);
          assert_eq!(d_red, vec![])
        }
      }

      // dup (dup dup)
      let dup_of_dupdup = t_str("(λ(1)1)(λ(1)1)λ(1)1");
      // depth 1 is is dup (dup dup) or (dup dup) (dup dup)
      let depth_1_terms = [dup_of_dupdup.clone(), t_str("((λ(1)1)λ(1)1)(λ(1)1)λ(1)1")];
      check_terms_present_in_depth_reductions(&dup_of_dupdup, 1, &depth_1_terms);
      // depth 2 is actually identical
      check_terms_present_in_depth_reductions(&dup_of_dupdup, 2, &depth_1_terms);
      check_terms_present_in_depth_reductions(&dup_of_dupdup, 3, &depth_1_terms);

      // (dup dup) dup 
      // output is (dup dup) dup
      let dupdup_of_dup = t_str("((λ(1)1)λ(1)1)λ(1)1");
      // since depth 1 is the same, all depths are the same
      let ans_terms = [dupdup_of_dup.clone()];
      for depth in 0..=4 {
        check_terms_present_in_depth_reductions(&dupdup_of_dup, depth, &ans_terms);
      }

      // \x. (id x) (id x) (id x) 
      // output is \x. x (id x) (id x) and so on (3) 
      // id x is (λ1)1
      let three_ids = t_str("λ(((λ1)1)(λ1)1)(λ1)1");
      let depth_1_terms = [t_str("λ((1)(λ1)1)(λ1)1"), t_str("λ(((λ1)1)1)(λ1)1"), t_str("λ(((λ1)1)(λ1)1)1")];
      check_terms_present_in_depth_reductions(&three_ids, 1, &depth_1_terms);
      let depth_2_terms = [t_str("λ((1)1)(λ1)1"), t_str("λ(((λ1)1)1)1"), t_str("λ((1)(λ1)1)1")];
      check_terms_present_in_depth_reductions(&three_ids, 2, &depth_2_terms);
      let depth_3_terms = [t_str("λ((1)1)1")];
      check_terms_present_in_depth_reductions(&three_ids, 3, &depth_3_terms);
    }
  }
