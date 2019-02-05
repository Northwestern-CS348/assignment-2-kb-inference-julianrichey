import read, copy
from util import *
from logical_classes import *

verbose = 0

class KnowledgeBase(object):
    def __init__(self, facts=[], rules=[]):
        self.facts = facts
        self.rules = rules
        self.ie = InferenceEngine()

    def __repr__(self):
        return 'KnowledgeBase({!r}, {!r})'.format(self.facts, self.rules)

    def __str__(self):
        string = "Knowledge Base: \n"
        string += "\n".join((str(fact) for fact in self.facts)) + "\n"
        string += "\n".join((str(rule) for rule in self.rules))
        return string

    def _get_fact(self, fact):
        """INTERNAL USE ONLY
        Get the fact in the KB that is the same as the fact argument

        Args:
            fact (Fact): Fact we're searching for

        Returns:
            Fact: matching fact
        """
        for kbfact in self.facts:
            if fact == kbfact:
                return kbfact

    def _get_rule(self, rule):
        """INTERNAL USE ONLY
        Get the rule in the KB that is the same as the rule argument

        Args:
            rule (Rule): Rule we're searching for

        Returns:
            Rule: matching rule
        """
        for kbrule in self.rules:
            if rule == kbrule:
                return kbrule

    def kb_add(self, fact_rule):
        """Add a fact or rule to the KB
        Args:
            fact_rule (Fact|Rule) - the fact or rule to be added
        Returns:
            None
        """
        printv("Adding {!r}", 1, verbose, [fact_rule])
        if isinstance(fact_rule, Fact):
            if fact_rule not in self.facts:
                self.facts.append(fact_rule)
                for rule in self.rules:
                    self.ie.fc_infer(fact_rule, rule, self)
            else:
                if fact_rule.supported_by:
                    ind = self.facts.index(fact_rule)
                    for f in fact_rule.supported_by:
                        self.facts[ind].supported_by.append(f)
                else:
                    ind = self.facts.index(fact_rule)
                    self.facts[ind].asserted = True
        elif isinstance(fact_rule, Rule):
            if fact_rule not in self.rules:
                self.rules.append(fact_rule)
                for fact in self.facts:
                    self.ie.fc_infer(fact, fact_rule, self)
            else:
                if fact_rule.supported_by:
                    ind = self.rules.index(fact_rule)
                    for f in fact_rule.supported_by:
                        self.rules[ind].supported_by.append(f)
                else:
                    ind = self.rules.index(fact_rule)
                    self.rules[ind].asserted = True

    def kb_assert(self, fact_rule):
        """Assert a fact or rule into the KB

        Args:
            fact_rule (Fact or Rule): Fact or Rule we're asserting
        """
        printv("Asserting {!r}", 0, verbose, [fact_rule])
        self.kb_add(fact_rule)

    def kb_ask(self, fact):
        """Ask if a fact is in the KB

        Args:
            fact (Fact) - Statement to be asked (will be converted into a Fact)

        Returns:
            listof Bindings|False - list of Bindings if result found, False otherwise
        """
        print("Asking {!r}".format(fact))
        if factq(fact):
            f = Fact(fact.statement)
            bindings_lst = ListOfBindings()
            # ask matched facts
            for fact in self.facts:
                binding = match(f.statement, fact.statement)
                if binding:
                    bindings_lst.add_bindings(binding, [fact])

            return bindings_lst if bindings_lst.list_of_bindings else []

        else:
            print("Invalid ask:", fact.statement)
            return []

    def kb_retract(self, fact):
        """Retract a fact from the KB

        Args:
            fact (Fact) - Fact to be retracted

        Returns:
            None
        """
        printv("Retracting {!r}", 0, verbose, [fact])
        ####################################################
        # Student code goes here

        #only remove fact if unsupported
        #never remove asserted rule
        #use supports_rules and supports_facts to find things to potentially retract
        #update supported_by lists
        #if fact/rule now has empty supported_by list and is not asserted, retract as well
        if isinstance(fact, Fact) and self.kb_ask(fact):
            kb_fact = self._get_fact(fact)
            kb_fact.asserted = False
            self.kb_retract_helper(fact)    #push problem onto helper function to handle rules

    #this gets called whenever a fact/rule that supports something gets retracted
    #helper used to both handle rules and to handle whether or not facts are asserted
    def kb_retract_helper(self, fact_or_rule):
        if isinstance(fact_or_rule, Fact):      #if input is fact
            kb_fact = self._get_fact(fact_or_rule)
            if kb_fact.asserted:                #if asserted, dont do anything
                return
            if not kb_fact.supported_by:            #if not supported iteratively check to delete supports
                for kb_facts in kb_fact.supports_facts:     #for facts
                    for pair in kb_facts.supported_by:
                        kb_facts.supported_by.remove(pair)
                    self.kb_retract_helper(kb_facts)        #go deeper
                for kb_rules in kb_fact.supports_rules:     #now for rules
                    for pair in kb_rules.supported_by:
                        kb_rules.supported_by.remove(pair)
                    self.kb_retract_helper(kb_rules)        #go deeper
                self.facts.remove(kb_fact)          #remove
        
        elif isinstance(fact_or_rule, Rule):        #if input is rule
            kb_rule = self._get_rule(fact_or_rule)
            if kb_rule.asserted:                    #if asserted, dont do anything
                return
            if not kb_rule.supported_by:                #if not supported iteratively check to delete supports
                for kb_facts in kb_rule.supports_facts:     #for facts
                    for pair in kb_facts.supported_by:
                        kb_facts.supported_by.remove(pair)
                    self.kb_retract_helper(kb_facts)        #go deeper
                for kb_rules in kb_rule.supports_rules:     #now for rules
                    for pair in kb_rules.supported_by:
                        kb_rules.supported_by.remove(pair)
                    self.kb_retract_helper(kb_rules)        #go deeper
                self.rules.remove(kb_rule)          #remove

class InferenceEngine(object):
    def fc_infer(self, fact, rule, kb):
        """Forward-chaining to infer new facts and rules

        Args:
            fact (Fact) - A fact from the KnowledgeBase
            rule (Rule) - A rule from the KnowledgeBase
            kb (KnowledgeBase) - A KnowledgeBase

        Returns:
            Nothing            
        """
        printv('Attempting to infer from {!r} and {!r} => {!r}', 1, verbose,
            [fact.statement, rule.lhs, rule.rhs])
        ####################################################
        # Student code goes here
        
        #add rule: check first element of lhs against facts in kb
            #if match, add new rule paired with *bindings* for that match
        #add fact: go through rules in kb checking first elem of lhs
        bindings = match(fact.statement, rule.lhs[0])
        if bindings:
            if len(rule.lhs)>1:     #if more than 1 term, this is a rule
                all_lhs = []
                for statements in rule.lhs[1:]:   #need to instantiate all lhs
                    all_lhs.append(instantiate(statements, bindings))
                new_rule = Rule([all_lhs, instantiate(rule.rhs, bindings)], [[fact, rule]])
                rule.supports_rules.append(new_rule)  #update lists for future retracting
                fact.supports_rules.append(new_rule)
                kb.kb_add(new_rule)             #add rule to kb
            else:                   #else there is 1 term, so it is a fact
                new_fact = Fact(instantiate(rule.rhs, bindings), [[fact, rule]])
                rule.supports_facts.append(new_fact)
                fact.supports_facts.append(new_fact)
                kb.kb_add(new_fact)             #add fact to kb