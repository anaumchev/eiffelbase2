-- Here you can try your own examples. Have fun! :)
class COMPLETENESS_CHECKS [G]
feature
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

end
