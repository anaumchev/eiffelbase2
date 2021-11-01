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

end
