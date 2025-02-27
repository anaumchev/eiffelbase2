﻿note
	description: "[
		Sequences of values, all of the same type or of a conforming one,
		accessible through integer indices in a contiguous interval.
	]"
	library: "Free implementation of ELKS library"
	status: "See notice at end of class."
	legal: "See notice at end of class."
	date: "$Date: 2021-07-13 16:53:18 +0300 (Tue, 13 Jul 2021) $"
	revision: "$Revision: 105634 $"

class ARRAY [G]

inherit

	RESIZABLE [G]
		redefine
			full, copy, is_equal, resizable
		end

	INDEXABLE [G, INTEGER]
		rename
			item as item alias "[]"
		redefine
			copy,
			is_equal,
			new_cursor
		end

	TO_SPECIAL [G]
		export
			{ARRAY} set_area
		redefine
			copy, is_equal, item, put, at, valid_index
		end

create
	make_empty,
	make,
	make_filled,
	make_from_array,
	make_from_special,
	make_from_cil

convert
	to_cil: {NATIVE_ARRAY [G]},
	to_special: {SPECIAL [G]},
	make_from_cil ({NATIVE_ARRAY [G]}),
 	to_mml_set: {MML_SET [G]},
 	to_mml_sequence: {MML_SEQUENCE [G]},
 	to_simple_array: {SIMPLE_ARRAY [G]}
 

feature -- Initialization

	make_empty
			-- Allocate empty array starting at `1'.
		do
			lower := 1
			upper := 0
			make_empty_area (0)
		ensure
			lower_set: lower = 1
			upper_set: upper = 0
			items_set: all_default
		end

	make_filled (a_default_value: G; min_index, max_index: INTEGER)
			-- Allocate array; set index interval to
			-- `min_index' .. `max_index'; set all values to default.
			-- (Make array empty if `min_index' = `max_index' + 1).
		require
			valid_bounds: min_index <= max_index + 1
		local
			n: INTEGER
		do
			lower := min_index
			upper := max_index
			if min_index <= max_index then
				n := max_index - min_index + 1
			end
			make_filled_area (a_default_value, n)
		ensure
			lower_set: lower = min_index
			upper_set: upper = max_index
			items_set: filled_with (a_default_value)
		end

	make (min_index, max_index: INTEGER)
			-- Allocate array; set index interval to
			-- `min_index' .. `max_index'; set all values to default.
			-- (Make array empty if `min_index' = `max_index' + 1).
		obsolete
			" `make' is not void-safe statically. Use `make_empty' or `make_filled' instead. [2017-05-31]"
		require
			valid_bounds: min_index <= max_index + 1
			has_default: min_index <= max_index implies ({G}).has_default
		do
			lower := min_index
			upper := max_index
			if min_index <= max_index then
				make_filled_area (({G}).default, max_index - min_index + 1)
			else
				make_empty_area (0)
			end
		ensure
			lower_set: lower = min_index
			upper_set: upper = max_index
			items_set: all_default
		end

	make_from_array (a: ARRAY [G])
			-- Initialize from the items of `a'.
			-- (Useful in proper descendants of class `ARRAY',
			-- to initialize an array-like object from a manifest array.)
		require
			array_exists: a /= Void
		do
			set_area (a.area)
			lower := a.lower
			upper := a.upper
		ensure
			shared: area = a.area
			lower_set: lower = a.lower
			upper_set: upper = a.upper
		end

	make_from_special (a: SPECIAL [G])
			-- Initialize Current from items of `a'.
		require
			special_attached: a /= Void
		do
			set_area (a)
			lower := 1
			upper := a.count
		ensure
			shared: area = a
			lower_set: lower = 1
			upper_set: upper = a.count
		end

	make_from_cil (na: NATIVE_ARRAY [like item])
			-- Initialize array from `na'.
		require
			is_dotnet: {PLATFORM}.is_dotnet
			na_not_void: na /= Void
		do
			create area.make_from_native_array (na)
			lower := 1
			upper := area.count
		end

feature -- Access

	item alias "[]", at alias "@" (i: INTEGER): G assign put
			-- Entry at index `i', if in index interval.
		do
			Result := area.item (i - lower)
		end

	entry (i: INTEGER): G
			-- Entry at index `i', if in index interval.
		require
			valid_key: valid_index (i)
		do
			Result := item (i)
		end

	has (v: G): BOOLEAN
			-- Does `v' appear in array?
			-- (Reference or object equality,
			-- based on `object_comparison'.)
		local
			i, nb: INTEGER
			l_area: like area
		do
			l_area := area
			nb := upper - lower
			if object_comparison and v /= Void then
				from
				until
					i > nb or Result
				loop
					Result := l_area.item (i) ~ v
					i := i + 1
				end
			else
				from
				until
					i > nb or Result
				loop
					Result := l_area.item (i) = v
					i := i + 1
				end
			end
		end

	new_cursor: ARRAY_ITERATION_CURSOR [G]
			-- <Precursor>
		note
			status: impure
		do
			create Result.make (Current)
		end

feature -- Measurement

	lower: INTEGER
			-- Minimum index.

	upper: INTEGER
			-- Maximum index.

	count, capacity: INTEGER
			-- Number of available indices.
		do
			Result := upper - lower + 1
		ensure then
			consistent_with_bounds: Result = upper - lower + 1
		end

	occurrences (v: G): INTEGER
			-- Number of times `v' appears in structure.
		local
			i: INTEGER
		do
			if object_comparison then
				from
					i := lower
				until
					i > upper
				loop
					if item (i) ~ v then
						Result := Result + 1
					end
					i := i + 1
				end
			else
				from
					i := lower
				until
					i > upper
				loop
					if item (i) = v then
						Result := Result + 1
					end
					i := i + 1
				end
			end
		end

feature -- Comparison

	is_equal (other: like Current): BOOLEAN
			-- Is array made of the same items as `other'?
		local
			i: INTEGER
		do
			if other = Current then
				Result := True
			elseif lower = other.lower and then upper = other.upper and then
				object_comparison = other.object_comparison
			then
				if object_comparison then
					from
						Result := True
						i := lower
					until
						not Result or i > upper
					loop
						Result := item (i) ~ other.item (i)
						i := i + 1
					end
				else
					Result := area.same_items (other.area, 0, 0, count)
				end
			end
		end

feature -- Status report

	all_default: BOOLEAN
			-- Are all items set to default values?
		do
			if count > 0 then
				Result := ({G}).has_default and then area.filled_with (({G}).default, 0, upper - lower)
			else
				Result := True
			end
		ensure
			definition: Result = (count = 0 or else
						((not attached item (upper) as i or else i = ({G}).default) and
							subarray (lower, upper - 1).all_default))
		end

	filled_with (v: G): BOOLEAN
			-- Are all items set to `v'?
		do
			Result := area.filled_with (v, 0, upper - lower)
		ensure
			definition: Result = (count = 0 or else
						(item (upper) = v and subarray (lower, upper - 1).filled_with (v)))
		end

	full: BOOLEAN
			-- Is structure filled to capacity?
			-- (Answer: yes)
		do
			Result := True
		end

	same_items (other: like Current): BOOLEAN
			-- Do `other' and Current have same items?
		require
			other_not_void: other /= Void
		do
			if count = other.count then
				Result := area.same_items (other.area, 0, 0, count)
			end
		ensure
			definition: Result = (count = other.count and then
				(count = 0 or else
					(item (upper) = other.item (other.upper) and
						subarray (lower, upper - 1).same_items
							(other.subarray (other.lower, other.upper - 1)))))
		end

	valid_index (i: INTEGER): BOOLEAN
			-- Is `i' within the bounds of the array?
		do
			Result := (lower <= i) and then (i <= upper)
		end

	extendible: BOOLEAN
			-- May items be added?
			-- (Answer: no, although array may be resized.)
		do
			Result := False
		end

	prunable: BOOLEAN
			-- May items be removed?
			-- (Answer: no.)
		do
			Result := False
		end

	resizable: BOOLEAN
			-- Can array be resized automatically?
		do
			Result := ({G}).has_default
		end

feature -- Element change

	put (v: like item; i: INTEGER)
			-- Replace `i'-th entry, if in index interval, by `v'.
		do
			area.put (v, i - lower)
		end

	enter (v: like item; i: INTEGER)
			-- Replace `i'-th entry, if in index interval, by `v'.
		require
			valid_key: valid_index (i)
		do
			area.put (v, i - lower)
		end

	force (v: like item; i: INTEGER)
			-- Assign item `v' to `i'-th entry.
			-- Resize the array if `i' falls out of currently defined bounds; preserve existing items.
			-- In void-safe mode, if ({G}).has_default does not hold, then you can only insert between
			-- `lower - 1' and `upper + 1' positions in the ARRAY.
		require
			has_default_if_too_low:
				(i < lower - 1 and lower /= {like lower}.min_value) implies ({G}).has_default
			has_default_if_too_high:
				(i > upper + 1 and upper /= {like upper}.max_value) implies ({G}).has_default
		local
			old_size, new_size: INTEGER
			new_lower, new_upper: INTEGER
			l_count, l_offset: INTEGER
			l_increased_by_one: BOOLEAN
		do
			new_lower := lower.min (i)
			new_upper := upper.max (i)
			new_size := new_upper - new_lower + 1
			l_increased_by_one := (i = upper + 1) or (i = lower - 1)
			if empty_area then
					-- The array is empty. First we create an empty SPECIAL of the right capacity.
				make_empty_area (new_size.max (additional_space))
				if new_lower < lower then
						-- The array is extended below lower.
					area.extend (v)
					if not l_increased_by_one then
							-- We need to fill the SPECIAL for `1' to `new_size - 1' with the default value.
						area.fill_with (({G}).default, 1, new_size - 1)
					end
				else
						-- The array is extended above upper.
					if not l_increased_by_one then
							-- We need to fill the SPECIAL for `0' to `new_size - 2' with the default value.
						area.fill_with (({G}).default, 0, new_size - 2)
					end
					area.extend (v)
				end
			else
				old_size := area.capacity
				if new_size > old_size then
					set_area (area.aliased_resized_area (new_size.max (old_size + additional_space)))
				end
				if new_lower < lower then
						-- We have inserted below the previous `lower'. We need to shift entries to the right
						-- before we can insert `v'.
					l_offset := lower - new_lower
					l_count := capacity
					if not l_increased_by_one and l_offset > l_count then
							-- With the `new_lower' given, the data has to move
							-- beyond the `area''s count which requires us to fill
							-- the gap between the old data's location and the new one
							-- with the default value.
						area.fill_with (({G}).default, l_count, l_offset - 1)
					end
					area.move_data (0, l_offset, l_count)
					if not l_increased_by_one then
							-- We start at `1' and not `0' because next instruction
							-- will update the item at position `0'.
						area.fill_with (({G}).default, 1, l_offset - 1)
					end
						-- Insert `v' at the new lower position.
					area.put (v, 0)
				else
					if new_size > area.count then
							-- We are adding to the new `upper' position. First we fill the non-initialized
							-- elements if any up to `new_size - 2' (i.e. up the the item prior to `upper').
						if not l_increased_by_one then
							area.fill_with (({G}).default, area.count, new_size - 2)
						end
							-- Add `v' at upper position.
						area.extend (v)
					else
							-- Here `lower' hasn't changed
						area.put (v, i - lower)
					end
				end
			end
			lower := new_lower
			upper := new_upper
		ensure
			inserted: item (i) = v
			higher_count: count >= old count
			lower_set: lower = (old lower).min (i)
			upper_set: upper = (old upper).max (i)
		end

	force_and_fill (v: like item; i: INTEGER)
			-- Assign item `v` to `i`-th entry.
			-- If `i` falls out of currently defined bounds:
			-- 	- Resize array as needed.
			-- 	- Fill in any new entry (in addition to the one at position `i` with value `v`).
			-- 	- Preserve existing items.
		local
			old_size, new_size: INTEGER
			new_lower, new_upper: INTEGER
			l_offset: INTEGER
		do
			new_lower := lower.min (i)
			new_upper := upper.max (i)
			new_size := new_upper - new_lower + 1
			old_size := area.capacity
			if old_size = 0 then
					-- The array is empty. First, create an empty SPECIAL of the right capacity.
				make_empty_area (new_size.max (additional_space))
					-- Fill the SPECIAL from `0` to `new_size - 1` with `v`.
				area.fill_with (v, 0, new_size - 1)
			else
				if new_size > old_size then
					set_area (area.aliased_resized_area (new_size.max (old_size + additional_space)))
				end
				if new_lower < lower then
						-- New items are below the previous `lower`.
						-- Shift entries towards `upper` before inserting `v`.
					l_offset := lower - new_lower
					area.move_data (0, l_offset, capacity)
						-- Fill new items with `v`.
					area.fill_with (v, 0, l_offset - 1)
				elseif new_size > area.count then
						-- Add new items above old `upper` position.
					area.fill_with (v, area.count, new_size - 1)
				else
						-- The item is changed inside the old boundaries.
					area.put (v, i - lower)
				end
			end
			lower := new_lower
			upper := new_upper
		ensure
			inserted: item (i) = v
			filled_below_lower: ∀ c: i |..| old lower ¦ c < old lower implies item (c) = v
			filled_above_upper: ∀ c: old upper |..| i ¦ c > old upper implies item (c) = v
			higher_count: count >= old count
			lower_set: lower = (old lower).min (i)
			upper_set: upper = (old upper).max (i)
		end

	fill_with (v: G)
			-- Set items between `lower' and `upper' with `v'.
		do
			area.fill_with (v, 0, upper - lower)
		ensure
			same_capacity: capacity = old capacity
			count_definition: count = old count
			filled: filled_with (v)
		end

	subcopy (other: ARRAY [like item]; start_pos, end_pos, index_pos: INTEGER)
			-- Copy items of `other' within bounds `start_pos' and `end_pos'
			-- to current array starting at index `index_pos'.
		require
			other_not_void: other /= Void
			valid_start_pos: start_pos >= other.lower
			valid_end_pos: end_pos <= other.upper
			valid_bounds: start_pos <= end_pos + 1
			valid_index_pos: index_pos >= lower
			enough_space: (upper - index_pos) >= (end_pos - start_pos)
		do
			area.copy_data (other.area, start_pos - other.lower, index_pos - lower, end_pos - start_pos + 1)
		ensure
				-- copied: forall `i' in 0 .. (`end_pos'-`start_pos'),
				--     item (index_pos + i) = other.item (start_pos + i)
		end

feature -- Iteration

	do_all (action: PROCEDURE [G])
			-- Apply `action' to every item, from first to last.
			-- Semantics not guaranteed if `action' changes the structure;
			-- in such a case, apply iterator to clone of structure instead.
		require
			action_not_void: action /= Void
		do
			area.do_all_in_bounds (action, 0, count - 1)
		end

	do_if (action: PROCEDURE [G]; test: FUNCTION [G, BOOLEAN])
			-- Apply `action' to every item that satisfies `test', from first to last.
			-- Semantics not guaranteed if `action' or `test' changes the structure;
			-- in such a case, apply iterator to clone of structure instead.
		require
			action_not_void: action /= Void
			test_not_void: test /= Void
		do
			area.do_if_in_bounds (action, test, 0, count - 1)
		end

	there_exists (test: FUNCTION [G, BOOLEAN]): BOOLEAN
			-- Is `test' true for at least one item?
		require
			test_not_void: test /= Void
		do
			Result := area.there_exists_in_bounds (test, 0, count - 1)
		end

	for_all (test: FUNCTION [G, BOOLEAN]): BOOLEAN
			-- Is `test' true for all items?
		require
			test_not_void: test /= Void
		do
			Result := area.for_all_in_bounds (test, 0, count - 1)
		end

	do_all_with_index (action: PROCEDURE [G, INTEGER])
			-- Apply `action' to every item, from first to last.
			-- `action' receives item and its index.
			-- Semantics not guaranteed if `action' changes the structure;
			-- in such a case, apply iterator to clone of structure instead.
		local
			i, j, nb: INTEGER
			l_area: like area
		do
			from
				i := 0
				j := lower
				nb := count - 1
				l_area := area
			until
				i > nb
			loop
				action.call ([l_area.item (i), j])
				j := j + 1
				i := i + 1
			end
		end

	do_if_with_index (action: PROCEDURE [G, INTEGER]; test: FUNCTION [G, INTEGER, BOOLEAN])
			-- Apply `action' to every item that satisfies `test', from first to last.
			-- `action' and `test' receive the item and its index.
			-- Semantics not guaranteed if `action' or `test' changes the structure;
			-- in such a case, apply iterator to clone of structure instead.
		local
			i, j, nb: INTEGER
			l_area: like area
		do
			from
				i := 0
				j := lower
				nb := count - 1
				l_area := area
			until
				i > nb
			loop
				if test.item ([l_area.item (i), j]) then
					action.call ([l_area.item (i), j])
				end
				j := j + 1
				i := i + 1
			end
		end

feature -- Removal

	wipe_out
			-- Make array empty.
		obsolete
			"Not applicable since not `prunable'. Use `discard_items' instead. [2017-05-31]"
		do
			discard_items
		end

	discard_items
			-- Reset all items to default values with reallocation.
		require
			has_default: ({G}).has_default
		do
			create area.make_filled (({G}).default, capacity)
		ensure
			default_items: all_default
		end

	clear_all
			-- Reset all items to default values.
		require
			has_default: ({G}).has_default
		do
			area.fill_with (({G}).default, 0, area.count - 1)
		ensure
			stable_lower: lower = old lower
			stable_upper: upper = old upper
			default_items: all_default
		end

	keep_head (n: INTEGER)
			-- Remove all items except for the first `n';
			-- do nothing if `n' >= `count'.
		require
			non_negative_argument: n >= 0
		do
			if n < count then
				upper := lower + n - 1
				area := area.aliased_resized_area (n)
			end
		ensure
			new_count: count = n.min (old count)
			same_lower: lower = old lower
		end

	keep_tail (n: INTEGER)
			-- Remove all items except for the last `n';
			-- do nothing if `n' >= `count'.
		require
			non_negative_argument: n >= 0
		local
			nb: INTEGER
		do
			nb := count
			if n < nb then
				area.overlapping_move (nb - n, 0, n)
				lower := upper - n + 1
				area := area.aliased_resized_area (n)
			end
		ensure
			new_count: count = n.min (old count)
			same_upper: upper = old upper
		end

	remove_head (n: INTEGER)
			-- Remove first `n' items;
			-- if `n' > `count', remove all.
		require
			n_non_negative: n >= 0
		do
			if n > count then
				lower := upper + 1
				area := area.aliased_resized_area (0)
			else
				keep_tail (count - n)
			end
		ensure
			new_count: count = (old count - n).max (0)
			same_upper: upper = old upper
		end

	remove_tail (n: INTEGER)
			-- Remove last `n' items;
			-- if `n' > `count', remove all.
		require
			n_non_negative: n >= 0
		do
			if n > count then
				upper := lower - 1
				area := area.aliased_resized_area (0)
			else
				keep_head (count - n)
			end
		ensure
			new_count: count = (old count - n).max (0)
			same_lower: lower = old lower
		end

feature -- Resizing

	grow (i: INTEGER)
			-- Change the capacity to at least `i'.
		do
			if i > capacity then
				conservative_resize_with_default (({G}).default, lower, upper + i - capacity)
			end
		end

	conservative_resize (min_index, max_index: INTEGER)
			-- Rearrange array so that it can accommodate
			-- indices down to `min_index' and up to `max_index'.
			-- Do not lose any previously entered item.
		obsolete
			" `conservative_resize' is not void-safe statically. Use `conservative_resize_with_default' instead. [2017-05-31]"
		require
			good_indices: min_index <= max_index
			has_default: ({G}).has_default
		do
			conservative_resize_with_default (({G}).default, min_index, max_index)
		ensure
			no_low_lost: lower = min_index or else lower = old lower
			no_high_lost: upper = max_index or else upper = old upper
		end

	conservative_resize_with_default (a_default_value: G; min_index, max_index: INTEGER)
			-- Rearrange array so that it can accommodate
			-- indices down to `min_index' and up to `max_index'.
			-- Do not lose any previously entered item.
		require
			good_indices: min_index <= max_index
		local
			new_size: INTEGER
			new_lower, new_upper: INTEGER
			offset: INTEGER
		do
			if empty_area then
				set_area (area.aliased_resized_area_with_default (a_default_value, max_index - min_index + 1))
				lower := min_index
				upper := max_index
			else
				new_lower := min_index.min (lower)
				new_upper := max_index.max (upper)
				new_size := new_upper - new_lower + 1
				if new_size > area.count then
					set_area (area.aliased_resized_area_with_default (a_default_value, new_size))
				end
				if new_lower < lower then
					offset := lower - new_lower
					area.move_data (0, offset, upper - lower + 1)
					area.fill_with (a_default_value, 0, offset - 1)
				end
				lower := new_lower
				upper := new_upper
			end
		ensure
			no_low_lost: lower = min_index or else lower = old lower
			no_high_lost: upper = max_index or else upper = old upper
		end

	resize (min_index, max_index: INTEGER)
			-- Rearrange array so that it can accommodate
			-- indices down to `min_index' and up to `max_index'.
			-- Do not lose any previously entered item.
		obsolete
			"Use `conservative_resize_with_default' instead as future versions will implement `resize' as specified in ELKS. [2017-05-31]"
		require
			good_indices: min_index <= max_index
			has_default: ({G}).has_default
		do
			conservative_resize_with_default (({G}).default, min_index, max_index)
		ensure
			no_low_lost: lower = min_index or else lower = old lower
			no_high_lost: upper = max_index or else upper = old upper
		end

	trim
			-- <Precursor>
		local
			n: like count
		do
			n := count
			if n < area.capacity then
				area := area.aliased_resized_area (n)
			end
		ensure then
			same_items: same_items (old twin)
		end

	rebase (a_lower: like lower)
			-- Without changing the actual content of `Current' we set `lower' to `a_lower'
			-- and `upper' accordingly to `a_lower + count - 1'.
		local
			l_old_lower: like lower
		do
			l_old_lower := lower
			lower := a_lower
			upper := a_lower + (upper - l_old_lower)
		ensure
			lower_set: lower = a_lower
			upper_set: upper = a_lower + old count - 1
		end

feature -- Conversion

	to_c: ANY
			-- Address of actual sequence of values,
			-- for passing to external (non-Eiffel) routines.
		require
			not_is_dotnet: not {PLATFORM}.is_dotnet
		do
			Result := area
		end

	to_cil: NATIVE_ARRAY [G]
			-- Address of actual sequence of values,
			-- for passing to external (non-Eiffel) routines.
		require
			is_dotnet: {PLATFORM}.is_dotnet
		do
			Result := area.native_array
		ensure
			to_cil_not_void: Result /= Void
		end

	to_special: SPECIAL [G]
			-- 'area'.
		do
			Result := area
		ensure
			to_special_not_void: Result /= Void
		end

	linear_representation: LINEAR [G]
			-- Representation as a linear structure.
		local
			temp: ARRAYED_LIST [G]
			i: INTEGER
		do
			create temp.make (capacity)
			from
				i := lower
			until
				i > upper
			loop
				temp.extend (item (i))
				i := i + 1
			end
			Result := temp
		end

feature -- Duplication

	copy (other: like Current)
			-- Reinitialize by copying all the items of `other'.
			-- (This is also used by `clone'.)
		do
			if other /= Current then
				standard_copy (other)
				set_area (other.area.twin)
			end
		ensure then
			equal_areas: area ~ other.area
		end

	subarray (start_pos, end_pos: INTEGER): ARRAY [G]
			-- Array made of items of current array within
			-- bounds `start_pos' and `end_pos'.
		require
			valid_start_pos: lower <= start_pos
			valid_end_pos: end_pos <= upper
			valid_bounds: (start_pos <= end_pos) or (start_pos = end_pos + 1)
		do
			if start_pos <= end_pos then
				create Result.make_filled (item (start_pos), start_pos, end_pos)
					-- Only copy elements if needed.
				Result.subcopy (Current, start_pos, end_pos, start_pos)
			else
					-- make empty
				create Result.make_empty
				Result.rebase (start_pos)
			end
		ensure
			lower: Result.lower = start_pos
			upper: Result.upper = end_pos
				-- copied: forall `i' in `start_pos' .. `end_pos',
				--     Result.item (i) = item (i)
		end

feature {NONE} -- Inapplicable

	prune (v: G)
			-- Remove first occurrence of `v' if any.
			-- (Precondition is False.)
		do
		end

	extend (v: G)
			-- Add `v' to structure.
			-- (Precondition is False.)
		do
		end

feature {NONE} -- Implementation

	empty_area: BOOLEAN
			-- Is `area' empty?
		do
			Result := area.capacity = 0
		end

feature -- Specification
 
 	to_mml_set: MML_SET [G]
 		do
 			check is_executable: False then end
 		end
 
 	to_mml_sequence: MML_SEQUENCE [G]
 		do
 			check is_executable: False then end
 		end
 
 	to_simple_array: SIMPLE_ARRAY [G]
 		do
 			check is_executable: False then end
 		end
 
invariant

	area_exists: area /= Void
	consistent_size: capacity = upper - lower + 1
	non_negative_count: count >= 0
	-- Internal discussion haven't reached an agreement on this invariant
	--	index_set_has_same_bounds: ((index_set.lower = lower) and
	--				(index_set.upper = lower + count - 1))

note
	copyright: "Copyright (c) 1984-2020, Eiffel Software and others"
	license: "Eiffel Forum License v2 (see http://www.eiffel.com/licensing/forum.txt)"
	source: "[
			Eiffel Software
			5949 Hollister Ave., Goleta, CA 93117 USA
			Telephone 805-685-1006, Fax 805-685-6869
			Website http://www.eiffel.com
			Customer support http://support.eiffel.com
		]"

end
