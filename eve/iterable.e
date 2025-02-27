note
	description: "Structure that can be iterated over using `across...loop...end'."
	library: "Free implementation of ELKS library"
	status: "See notice at end of class."
	legal: "See notice at end of class."
	date: "$Date: 2018-09-13 19:59:10 +0300 (Thu, 13 Sep 2018) $"
	revision: "$Revision: 102164 $"

deferred class
	ITERABLE [G]

feature -- Access

	new_cursor: ITERATION_CURSOR [G]
			-- Fresh cursor associated with current structure
		note
			status: impure
		deferred
		ensure
			result_attached: Result /= Void
			closed: closed
			result_fresh: Result.is_fresh
			result_wrapped: Result.is_wrapped and Result.inv
			result_in_observers: observers = old observers & Result
			modify_field (["observers", "closed"], Current)
		end

note
	copyright: "Copyright (c) 1984-2012, Eiffel Software and others"
	license:   "Eiffel Forum License v2 (see http://www.eiffel.com/licensing/forum.txt)"
	source: "[
			Eiffel Software
			5949 Hollister Ave., Goleta, CA 93117 USA
			Telephone 805-685-1006, Fax 805-685-6869
			Website http://www.eiffel.com
			Customer support http://support.eiffel.com
		]"


end
