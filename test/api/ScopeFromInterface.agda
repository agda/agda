module _ where

import Issue1168       ;  module I = Issue1168
import PrettyInterface ;  module P = PrettyInterface

id : {A : Set} → A → A
id {A = A} a = a
