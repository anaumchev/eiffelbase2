note explicit:wrapping
class COMPLETENESS_CHECKS [G]
feature

    v_arrayed_list_extend_at (al1, al2: V_ARRAYED_LIST [G]; v: G; i: INTEGER)
    	require
            al1.is_equal_ (al2)
            across al1.observers as o all o.item.is_open end
            across al2.observers as o all o.item.is_open end
            modify (al1, al2)
            al1.has_index (i)
        do
            al1.extend_at (v, i)
            al2.extend_at (v, i)
        ensure
            al1.is_equal_ (al2)
        end

    v_arrayed_list_extend_back (al1, al2: V_ARRAYED_LIST [G]; v: G)
    	require
            al1.is_equal_ (al2)
            across al1.observers as o all o.item.is_open end
            across al2.observers as o all o.item.is_open end
            modify (al1, al2)
        do
            al1.extend_back (v)
            al2.extend_back (v)
        ensure
            al1.is_equal_ (al2)
        end

    v_arrayed_list_extend_front (al1, al2: V_ARRAYED_LIST [G]; v: G)
    	require
            al1.is_equal_ (al2)
            across al1.observers as o all o.item.is_open end
            across al2.observers as o all o.item.is_open end
            modify (al1, al2)
        do
            al1.extend_front (v)
            al2.extend_front (v)
        ensure
            al1.is_equal_ (al2)
        end    
    
    v_arrayed_list_put (al1, al2: V_ARRAYED_LIST [G]; v: G; i: INTEGER)
    	require
            al1.is_equal_ (al2)
            al1.has_index (i)
            across al1.observers as o all o.item.is_open end
            across al2.observers as o all o.item.is_open end
            modify (al1, al2)
        do
            al1.put (v, i)
            al2.put (v, i)
        ensure
            al1.is_equal_ (al2)
        end
    
    v_arrayed_list_at (al1, al2: V_ARRAYED_LIST [G]; i: INTEGER)
    	require
            al1.is_equal_ (al2)
            al1.has_index (i)
            modify_field (["observers", "closed"], [al1, al2])
        local
            ali1, ali2: V_ARRAYED_LIST_ITERATOR [G]
        do
            ali1 := al1.at (i)
            ali2 := al2.at (i)
            check ali1.is_equal_ (ali2) end
        end    
    
    v_arrayed_list_item (al1, al2: V_ARRAYED_LIST [G]; i: INTEGER)
    	require
            al1.is_equal_ (al2)
            al1.has_index (i)
        do
        ensure
            al1.item (i) ~ al2.item (i)
        end    
    
    v_arrayed_list_copy (al1, al2, other: V_ARRAYED_LIST [G])
    	require
            across al1.observers as o all o.item.is_open end
            across al2.observers as o all o.item.is_open end
            modify_model ("sequence", [al1, al2])
            modify_field ("closed", other)
            al1.is_equal_ (al2)
        do
            al1.copy_ (other)
            al2.copy_ (other)
        ensure
            al1.is_equal_ (al2)
        end    
    
    v_arrayed_list_default_create
        local
            al1, al2: V_ARRAYED_LIST [G]
        do
            create al1
            create al2
            check al1.is_equal_ (al2) end
        end
    
    v_array_iterator_put (ai1, ai2: V_ARRAY_ITERATOR [G]; v: G)
    	require
            ai1.is_equal_ (ai2)
            ai1 /= ai2
            not ai1.off
            not ai2.off
            across ai1.target.observers as o all o.item /= Current implies o.item.is_open end
            across ai2.target.observers as o all o.item /= Current implies o.item.is_open end
            modify_model (["sequence", "box"], [ai1, ai2])
	    modify_model ("bag", [ai1.target, ai2.target])
        do
            ai1.put (v)
            ai2.put (v)
        ensure
            ai1.is_equal_ (ai2)
        end

    v_array_iterator_target  (ai1, ai2: V_ARRAY_ITERATOR [G])
    	require
            ai1.is_equal_ (ai2)
        do
        ensure
            ai1.target ~ ai2.target
        end

    v_array_iterator_copy_  (ai1, ai2, other: V_ARRAY_ITERATOR [G])
    	require
            target_wrapped: ai1.target.is_wrapped
            target_wrapped: ai2.target.is_wrapped
            other_target_wrapped: other.target.is_wrapped
            modify (ai1, ai2)
            modify_model ("observers", [ai1.target, ai2.target, other.target])
            ai1.is_equal_ (ai2)
            ai1 /= other
        do
            ai1.copy_ (other)
            ai2.copy_ (other)
        ensure
            ai1.is_equal_ (ai2)
        end

    v_array2_flat_put  (a1, a2: V_ARRAY2 [G]; v: G; i: INTEGER)
    	require
            a1.has_index (i)
            observers_open: across a1.observers as o all o.item.is_open end
            observers_open: across a2.observers as o all o.item.is_open end
            modify_model ("sequence", [a1, a2])
            a1.is_equal_ (a2)
        do
            a1.flat_put (v, i)
            a2.flat_put (v, i)
        ensure
            a1.is_equal_ (a2)
        end

    v_array2_put (a1, a2: V_ARRAY2 [G]; v: G; i, j: INTEGER)
    	require
            valid_row: a1.has_row (i)
            valid_column: a1.has_column (j)
            observers_open: across a1.observers as o all o.item.is_open end
            observers_open: across a2.observers as o all o.item.is_open end
            modify_model ("sequence", [a1, a2])
            a1.is_equal_ (a2)
        do
            a1.put (v, i, j)
            a2.put (v, i, j)
        ensure
            a1.is_equal_ (a2)
        end

    v_array2_flat_at  (a1, a2: V_ARRAY2 [G]; i: INTEGER)
        require
            a1.is_equal_ (a2)
            modify (a1, a2)
        local
            ai1, ai2: V_ARRAY_ITERATOR [G]
        do
            ai1 := a1.flat_at (i)
            ai2 := a2.flat_at (i)
            check ai1.is_equal_ (ai2) end
        end

    v_array2_has_column (a1, a2: V_ARRAY2 [G]; i: INTEGER)
        require
            a1.is_equal_ (a2)
        do
        ensure
            a1.has_column (i) = a2.has_column (i)
        end

    v_array2_has_row (a1, a2: V_ARRAY2 [G]; i: INTEGER)
        require
            a1.is_equal_ (a2)
        do
        ensure
            a1.has_row (i) = a2.has_row (i)
        end

    v_array2_upper (a1, a2: V_ARRAY2 [G])
        require
            a1.is_equal_ (a2)
        do
        ensure
            a1.upper = a2.upper
        end

    v_array2_Lower (a1, a2: V_ARRAY2 [G])
        require
            a1.is_equal_ (a2)
        do
        ensure
            a1.Lower = a2.Lower
        end

    v_array2_column_index (a1, a2: V_ARRAY2 [G]; i: INTEGER)
        require
            non_empty: a1.column_count > 0
            a1.is_equal_ (a2)
        do
        ensure
            a1.column_index (i) = a2.column_index (i)
        end

    v_array2_row_index (a1, a2: V_ARRAY2 [G]; i: INTEGER)
    	require
	    non_empty: a1.column_count > 0
	    a1.is_equal_ (a2)
	do
        ensure
    	    a1.row_index (i) = a2.row_index (i)
        end

    v_array2_flat_index (a1, a2: V_ARRAY2 [G]; i, j: INTEGER)
    	require
	    1 <= i and i <= a1.row_count
	    1 <= j and j <= a1.column_count
	    a1.is_equal_ (a2)
	do
        ensure
    	    a1.flat_index (i, j) = a2.flat_index (i, j)
        end

    v_array2_column_count (a1, a2: V_ARRAY2 [G])
    	require
	    a1.is_equal_ (a2)
	do
        ensure
    	    a1.count = a2.count
        end

    v_array2_column_count (a1, a2: V_ARRAY2 [G])
    	require
	    a1.is_equal_ (a2)
	do
        ensure
    	    a1.column_count = a2.column_count
        end

    v_array2_row_count (a1, a2: V_ARRAY2 [G])
    	require
	    a1.is_equal_ (a2)
	do
        ensure
    	    a1.row_count = a2.row_count
        end

    v_array2_flat_item (a1, a2: V_ARRAY2 [G]; i: INTEGER)
    	require
	    a1.is_equal_ (a2)
            a1.has_index (i)
	do
        ensure
    	    a1.flat_item (i) ~ a2.flat_item (i)
        end

    v_array2_item (a1, a2: V_ARRAY2 [G]; i, j: INTEGER)
    	require
	    a1.is_equal_ (a2)
	    valid_row: a1.has_row (i)
	    valid_column: a1.has_column (j)
	do
        ensure
    	    a1.item (i, j) ~ a2.item (i, j)
        end

    v_array2_copy_ (a1, a2, other: V_ARRAY2 [G])
        require
	    a1.is_equal_ (a2)
            modify (a1, a2, other)
            across a1.observers as o all o.item.is_open end
            across a2.observers as o all o.item.is_open end
	do
            a1.copy_ (other)
            a2.copy_ (other)
        ensure
    	    a1.is_equal_ (a2)
        end

    v_array2_make_filled (n, m: INTEGER; v: G)
    	require
	    valid_dimensions: (n = 0 and m = 0) or (n > 0 and m > 0)
        local
            a1, a2: V_ARRAY2 [G]
	do
            create a1.make_filled (n, m, v)
            create a2.make_filled (n, m, v)
            check a1.is_equal_ (a2) end
        end

    v_array2_make (n, m: INTEGER)
    	require
	    valid_dimensions: (n = 0 and m = 0) or (n > 0 and m > 0)
        local
            a1, a2: V_ARRAY2 [G]
	do
            create a1.make (n, m)
            create a2.make (n, m)
            check a1.is_equal_ (a2) end
        end

    v_linked_stack_wipe_out (ls1, ls2: V_LINKED_STACK [G])
        require
            ls1.is_equal_ (ls2)
            modify (ls1, ls2)
            ls1.observers.is_empty
            ls2.observers.is_empty
        do
            ls1.wipe_out
            ls2.wipe_out
        ensure
            ls1.is_equal_ (ls2)
        end

    v_linked_stack_remove (ls1, ls2: V_LINKED_STACK [G])
        require
            ls1.is_equal_ (ls2)
            modify (ls1, ls2)
            ls1.observers.is_empty
            ls2.observers.is_empty
            not ls1.is_empty
            not ls2.is_empty
            ls1 /= ls2
        do
            ls1.remove
            ls2.remove
        ensure
            ls1.is_equal_ (ls2)
        end

    v_linked_stack_extend (ls1, ls2: V_LINKED_STACK [G]; v: G)
        require
            ls1.is_equal_ (ls2)
            modify (ls1, ls2)
            ls1.observers.is_empty
            ls2.observers.is_empty
        do
            ls1.extend (v)
            ls2.extend (v)
        ensure
            ls1.is_equal_ (ls2)
        end

    v_array_make (l, u: INTEGER)
        require
            l <= u + 1
        local
            a1, a2: V_ARRAY [G]
        do
            create a1.make (l, u)
            create a2.make (l, u)
            check a1.is_equal_(a2) end
        end

    v_array_make_filled (l, u: INTEGER; v: G)
        require
            l <= u + 1
        local
            a1, a2: V_ARRAY [G]
        do
            create a1.make_filled (l, u, v)
            create a2.make_filled (l, u, v)
            check a1.is_equal_(a2) end
        end

    v_array_item (a1, a2: V_ARRAY [G]; i: INTEGER; v: G)
        require
            a1.is_equal_ (a2)
            a1.has_index (i)
        do
        ensure
            a1.item (i) = a2.item (i)
        end
        
    v_array_subarray (a1, a2: V_ARRAY [G]; l, u: INTEGER; v: G)
        note
            explicit: wrapping
        require
            a1.is_equal_ (a2)
    	    l_not_too_small: l >= a1.lower_
	    u_not_too_large: u <= a2.upper_
	    l_not_too_large: l <= u + 1
            modify_model ("observers", a1)
            modify_model ("observers", a2)            
        local
            a1_sub, a2_sub: V_ARRAY [G]
        do
            a1_sub := a1.subarray (l, u)
            a2_sub := a2.subarray (l, u)
            check a1_sub.is_equal_ (a2_sub) end
        end

    v_array_lower_upper_count (a1, a2: V_ARRAY [G])
        require
            a1.is_equal_ (a2)
        do
        ensure
            a1.lower = a2.lower
            a1.upper = a2.upper
            a1.count = a2.count
        end
	
    v_array_at (a1, a2: V_ARRAY [G]; i: INTEGER)
        note
            explicit: wrapping
        require
            a1.is_equal_ (a2)
            a1.has_index (i)
            modify (a1, a2)
        local
            i1, i2: V_ARRAY_ITERATOR [G]
        do
            i1 := a1.at (i)
            i2 := a2.at (i)
            check i1.is_equal_ (i2) end
        end
	
    v_array_put (a1, a2: V_ARRAY [G]; v: G; i: INTEGER)
        note
            explicit: wrapping
        require
            a1.is_equal_ (a2)
            a1.has_index (i)
            across a1.observers as o all o.item.is_open end
            across a2.observers as o all o.item.is_open end
            modify (a1, a2)
        do
            a1.put (v, i)
            a2.put (v, i)
        ensure
            a1.is_equal_ (a2)
        end

    v_array_fill (a1, a2: V_ARRAY [G]; v: G; l, u: INTEGER)
        note
            explicit: wrapping
        require
            a1.is_equal_ (a2)
            l_not_too_small: l >= a1.lower_
	    u_not_too_large: u <= a1.upper_
	    l_not_too_large: l <= u + 1
            across a1.observers as o all o.item.is_open end
            across a2.observers as o all o.item.is_open end
            modify (a1, a2)
        do
            a1.fill (v, l, u)
            a2.fill (v, l, u)
        ensure
            a1.is_equal_ (a2)
        end

    v_array_clear (a1, a2: V_ARRAY [G]; l, u: INTEGER)
        note
            explicit: wrapping
        require
            a1.is_equal_ (a2)
            l_not_too_small: l >= a1.lower_
	    u_not_too_large: u <= a1.upper_
	    l_not_too_large: l <= u + 1
            across a1.observers as o all o.item.is_open end
            across a2.observers as o all o.item.is_open end
            modify (a1, a2)
        do
            a1.clear (l, u)
            a2.clear (l, u)
        ensure
            a1.is_equal_ (a2)
        end

    v_array_copy_range_within (a1, a2: V_ARRAY [G]; fst, lst, index: INTEGER)
        note
            explicit: wrapping
        require
            a1.is_equal_ (a2)
    	    first_not_too_small: fst >= a1.lower_
	    last_not_too_large: lst <= a1.upper_
	    first_not_too_large: fst <= lst + 1
	    index_not_too_small: index >= a1.lower_
	    enough_space: a1.upper_ - index >= lst - fst
            across a1.observers as o all o.item.is_open end
            across a2.observers as o all o.item.is_open end
            modify (a1, a2)
        do
            a1.copy_range_within (fst, lst, index)
            a2.copy_range_within (fst, lst, index)
        ensure
            a1.is_equal_ (a2)
        end

    v_array_resize (a1, a2: V_ARRAY [G]; l, u: INTEGER)
        note
            explicit: wrapping
        require
            a1.is_equal_ (a2)
    	    valid_indexes: l <= u + 1
            across a1.observers as o all o.item.is_open end
            across a2.observers as o all o.item.is_open end
            modify_model (["sequence", "lower_"], [a1, a2])
        do
            a1.resize (l, u)
            a2.resize (l, u)
        ensure
            a1.is_equal_ (a2)
        end

    v_array_include (a1, a2: V_ARRAY [G]; i: INTEGER)
        note
            explicit: wrapping
        require
            a1.is_equal_ (a2)
            across a1.observers as o all o.item.is_open end
            across a2.observers as o all o.item.is_open end
            modify_model (["sequence", "lower_"], [a1, a2])
        do
            a1.include (i)
            a2.include (i)
        ensure
            a1.is_equal_ (a2)
        end
	
    v_array_force (a1, a2: V_ARRAY [G]; i: INTEGER; v: G)
        note
            explicit: wrapping
        require
            a1.is_equal_ (a2)
            across a1.observers as o all o.item.is_open end
            across a2.observers as o all o.item.is_open end
            modify_model (["sequence", "lower_"], [a1, a2])
        do
            a1.force (v, i)
            a2.force (v, i)
        ensure
            a1.is_equal_ (a2)
        end

    v_array_wipe_out (a1, a2: V_ARRAY [G])
        note
            explicit: wrapping
        require
            a1.is_equal_ (a2)
            across a1.observers as o all o.item.is_open end
            across a2.observers as o all o.item.is_open end
            modify_model (["sequence", "lower_"], [a1, a2])
        do
            a1.wipe_out
            a2.wipe_out
        ensure
            a1.is_equal_ (a2)
        end

   v_linked_stack_default_create
        local
            ls1, ls2: V_LINKED_STACK [G]
        do
            create ls1
            create ls2
            check ls1.is_equal_(ls2) end
        end
	
    v_linked_stack_item (ls1, ls2: V_LINKED_STACK [G])
        require
            ls1.is_equal_ (ls2)
            not ls1.is_empty
        do
        ensure
            ls1.item = ls2.item
        end
	
    v_linked_stack_count (ls1, ls2: V_LINKED_STACK [G])
        require
            ls1.is_equal_ (ls2)
        do
        ensure
            ls1.count = ls2.count
        end

    v_linked_stack_new_cursor (ls1, ls2: V_LINKED_STACK [G])
        require
            ls1.is_equal_ (ls2)
            modify (ls1, ls2)
        local
            lsi1, lsi2: V_LINKED_STACK_ITERATOR [G]
        do
            lsi1 := ls1.new_cursor
            lsi2 := ls2.new_cursor
            check target: ls1.is_equal_ (ls2) end
            check return: lsi1.is_equal_ (lsi2) end
        end

end
